import GaloisForLFunctions.RHTower.ModularLambdaWindingLog
import GaloisForLFunctions.HTGeometry.ModularFundamentalDomainVolume

/-!
# Mass and Dirichlet energy of the `λ`-test functions

With `L = lambdaLog` a holomorphic logarithm of the modular `λ` on the upper half-plane, a profile
`κ : ℝ → ℝ` and `N ∈ ℕ`, put (`lambdaTest`)

`f(τ) = e^{i Im L(τ)/N} κ(Re L(τ))`,   i.e.  `f = (λ/|λ|)^{1/N} κ(log|λ|)`.

* **Invariance** (`lambdaTest_smul`): `f(gτ) = f(τ)` for `g` in the winding subgroup `Γ_N`, because
  `L(gτ) = L(τ) + 2πi w(g)` with `N ∣ w(g)`.
* **Mass** (`lintegral_norm_sq_lambdaTest_ge`): `|f| = |κ(Re L)|`. On a compact `K ⊂ ℍ` the function
  `Re L` is bounded, so once `κ = 1` on `[−L, L]` with `L` large, every `D ⊇ K` carries hyperbolic
  mass `∫_D |f|² dμ ≥ μ(K)`, uniformly in `N`.
* **Gradient** (`norm_sq_fderiv_lambdaTest`): `|∂ₓf|² + |∂ᵧf|² = |L'|² (κ'(Re L)² + κ(Re L)²/N²)`, by
  the chain rule and the Cauchy–Riemann equations for `L`.
* **Energy** (`lintegral_norm_sq_fderiv_lambdaTest_le`): if `λ` is injective on a measurable
  `D ⊂ ℍ`, then
  `∫_D (|∂ₓf|² + |∂ᵧf|²) dx dy ≤ 2π ∫_ℝ (κ'² + κ²/N²)`.
  The integrand is `|λ'|²·G(log|λ|)/|λ|²` with `G = κ'² + κ²/N²`. The holomorphic change of variables
  `z = λ(τ)` (Jacobian `|λ'|²`) turns it into `∫_{λ(D)} G(log|z|)/|z|² dA ≤ ∫_ℂ G(log|z|)/|z|² dA`.
  In polar coordinates `z = e^{s+iθ}` this is `2π ∫ G(s) ds`.
-/

open Filter Topology Set MeasureTheory UpperHalfPlane
open scoped MatrixGroups

namespace GaloisForLFunctions.RHTower.ModularLambdaWinding

open GaloisForLFunctions.HTGeometry Bottcher

noncomputable section

/-- **The `λ`-test function** `f(τ) = e^{i Im L(τ)/N} κ(Re L(τ))`. -/
def lambdaTest (κ : ℝ → ℝ) (N : ℕ) (τ : ℂ) : ℂ :=
  Complex.exp (Complex.I * (((lambdaLog τ).im / N : ℝ) : ℂ)) * (κ (lambdaLog τ).re : ℂ)

theorem norm_cexp_I_mul_real_eq_one (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x

theorem norm_lambdaTest (κ : ℝ → ℝ) (N : ℕ) (τ : ℂ) :
    ‖lambdaTest κ N τ‖ = |κ (lambdaLog τ).re| := by
  rw [lambdaTest, norm_mul, norm_cexp_I_mul_real_eq_one, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- **Invariance under the winding subgroup.** -/
theorem lambdaTest_smul (κ : ℝ → ℝ) {N : ℕ} {g : SL(2, ℤ)} (hg : g ∈ windingSubgroup N)
    (τ : ℍ) : lambdaTest κ N ((g • τ : ℍ) : ℂ) = lambdaTest κ N τ := by
  obtain ⟨hg2, k, hk⟩ := mem_windingSubgroup.1 hg
  have h := lambdaLog_smul hg2 τ
  rw [hk] at h
  unfold lambdaTest
  rw [h]
  have hre : (lambdaLog (τ : ℂ) + 2 * Real.pi * Complex.I * ((((N : ℤ) * k : ℤ)) : ℂ)).re =
      (lambdaLog τ).re := by simp
  have him : (lambdaLog (τ : ℂ) + 2 * Real.pi * Complex.I * ((((N : ℤ) * k : ℤ)) : ℂ)).im =
      (lambdaLog τ).im + 2 * Real.pi * ((N : ℝ) * k) := by simp
  rw [hre, him]
  congr 1
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  · have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    rw [show ((lambdaLog (τ : ℂ)).im + 2 * Real.pi * ((N : ℝ) * k)) / N =
        (lambdaLog (τ : ℂ)).im / N + 2 * Real.pi * k by field_simp]
    push_cast
    rw [mul_add, Complex.exp_add,
      show Complex.I * (2 * Real.pi * (k : ℂ)) = (k : ℂ) * (2 * Real.pi * Complex.I) by ring,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ### Mass -/

theorem continuous_re_lambdaLog : Continuous fun τ : ℍ => (lambdaLog τ).re :=
  Complex.continuous_re.comp (continuousOn_iff_continuous_restrict.1 continuousOn_lambdaLog |>.comp
    (show Continuous fun τ : ℍ => (⟨(τ : ℂ), τ.im_pos⟩ : {z : ℂ | 0 < z.im}) by fun_prop))

/-- **Mass on every set containing a fixed compact set.** For compact `K ⊂ ℍ` there is `L₀` such
that, whenever `κ = 1` on `[−L, L]` with `L ≥ L₀`, every `D ⊇ K` has `∫_D |f|² dμ ≥ μ(K)`. -/
theorem lintegral_norm_sq_lambdaTest_ge {K : Set ℍ} (hK : IsCompact K) :
    ∃ L₀ : ℝ, ∀ {κ : ℝ → ℝ} {L : ℝ}, L₀ ≤ L → (∀ t, |t| ≤ L → κ t = 1) → ∀ (N : ℕ)
      {D : Set ℍ}, K ⊆ D →
        volume K ≤ ∫⁻ τ in D, ENNReal.ofReal (‖lambdaTest κ N τ‖ ^ 2) := by
  obtain ⟨L₀, hL₀⟩ := hK.exists_bound_of_continuousOn continuous_re_lambdaLog.continuousOn
  refine ⟨L₀, fun {κ} {L} hL hκ N D hKD => ?_⟩
  calc volume K = ∫⁻ _τ in K, (1 : ENNReal) := by rw [setLIntegral_const, one_mul]
    _ = ∫⁻ τ in K, ENNReal.ofReal (‖lambdaTest κ N τ‖ ^ 2) := by
        refine setLIntegral_congr_fun hK.isClosed.measurableSet fun τ hτ => ?_
        have h := hL₀ τ hτ
        rw [Real.norm_eq_abs] at h
        rw [norm_lambdaTest, hκ _ (h.trans hL)]
        simp
    _ ≤ _ := lintegral_mono_set hKD

theorem isCompact_closedBall_upperHalfPlane (τ₀ : ℍ) (r : ℝ) :
    IsCompact (Metric.closedBall τ₀ r) := isCompact_closedBall τ₀ r

theorem volume_closedBall_upperHalfPlane_pos (τ₀ : ℍ) {r : ℝ} (hr : 0 < r) :
    0 < volume (Metric.closedBall τ₀ r) :=
  lt_of_lt_of_le (Metric.isOpen_ball.measure_pos volume ⟨τ₀, Metric.mem_ball_self hr⟩)
    (measure_mono Metric.ball_subset_closedBall)

/-! ### The gradient -/

theorem hasDerivAt_lambdaLog {τ : ℂ} (hτ : 0 < τ.im) : HasDerivAt lambdaLog (deriv lambdaLog τ) τ :=
  (differentiableOn_lambdaLog.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hτ)).hasDerivAt

/-- `‖e^{iθ}(a₁ + i a₂)‖² = a₁² + a₂²`. -/
theorem norm_sq_exp_mul (θ a₁ a₂ : ℝ) :
    ‖Complex.exp (Complex.I * (θ : ℂ)) * ((a₁ : ℂ) + Complex.I * (a₂ : ℂ))‖ ^ 2 = a₁ ^ 2 + a₂ ^ 2 := by
  rw [norm_mul, norm_cexp_I_mul_real_eq_one, one_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp
  ring

/-- The real derivative of `z ↦ e^{i Im z/N} κ(Re z)`. -/
theorem hasFDerivAt_testProfile (κ : ℝ → ℝ) (N : ℕ) {w : ℂ} (hκ : DifferentiableAt ℝ κ w.re) :
    ∃ E' : ℂ →L[ℝ] ℂ, HasFDerivAt
        (fun z : ℂ => Complex.exp (Complex.I * ((z.im / N : ℝ) : ℂ)) * (κ z.re : ℂ)) E' w ∧
      ∀ h : ℂ, E' h = Complex.exp (Complex.I * ((w.im / N : ℝ) : ℂ)) *
        (((deriv κ w.re * h.re : ℝ) : ℂ) + Complex.I * ((κ w.re * h.im / N : ℝ) : ℂ)) := by
  let L₁ : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp ((N : ℝ)⁻¹ • Complex.imCLM)
  have hL₁ : ∀ z : ℂ, ((z.im / N : ℝ) : ℂ) = L₁ z := fun z => by
    simp [L₁, div_eq_inv_mul]
  have h1 : HasFDerivAt (fun z : ℂ => Complex.I * ((z.im / N : ℝ) : ℂ)) (Complex.I • L₁) w := by
    refine ((L₁.hasFDerivAt (x := w)).const_smul Complex.I).congr_of_eventuallyEq
      (Eventually.of_forall fun z => ?_)
    show Complex.I * ((z.im / N : ℝ) : ℂ) = Complex.I • L₁ z
    rw [hL₁, smul_eq_mul]
  have h2 := h1.cexp
  have h3 : HasFDerivAt (fun z : ℂ => (κ z.re : ℂ))
      (Complex.ofRealCLM.comp (deriv κ w.re • Complex.reCLM)) w := by
    have hk := (hκ.hasDerivAt).comp_hasFDerivAt w Complex.reCLM.hasFDerivAt
    exact Complex.ofRealCLM.hasFDerivAt.comp w hk
  refine ⟨_, h2.mul h3, fun h => ?_⟩
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.reCLM_apply, smul_eq_mul, L₁,
    Complex.imCLM_apply]
  push_cast
  field_simp

/-- **The pointwise Dirichlet density** `|∂ₓf|² + |∂ᵧf|² = |L'|²(κ'(Re L)² + κ(Re L)²/N²)`. -/
theorem norm_sq_fderiv_lambdaTest (κ : ℝ → ℝ) (N : ℕ) {τ : ℂ} (hτ : 0 < τ.im)
    (hκ : DifferentiableAt ℝ κ (lambdaLog τ).re) :
    ‖fderiv ℝ (lambdaTest κ N) τ 1‖ ^ 2 + ‖fderiv ℝ (lambdaTest κ N) τ Complex.I‖ ^ 2 =
      ‖deriv lambdaLog τ‖ ^ 2 *
        (deriv κ (lambdaLog τ).re ^ 2 + κ (lambdaLog τ).re ^ 2 / (N : ℝ) ^ 2) := by
  obtain ⟨E', hE, hE'⟩ := hasFDerivAt_testProfile κ N hκ
  have hL := (hasDerivAt_lambdaLog hτ).hasFDerivAt.restrictScalars ℝ
  have hcomp := hE.comp τ hL
  have hfd : fderiv ℝ (lambdaTest κ N) τ =
      E'.comp ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv lambdaLog τ)).restrictScalars ℝ) :=
    hcomp.fderiv
  rw [hfd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, hE',
    smul_eq_mul]
  rw [norm_sq_exp_mul, norm_sq_exp_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, one_mul, zero_mul,
    zero_add, zero_sub]
  rcases eq_or_ne (N : ℝ) 0 with hN | hN
  · rw [hN]; simp; ring
  · field_simp
    ring

/-! ### The energy bound -/

/-- `L' = λ'/λ` and `Re L = log |λ|`. -/
theorem deriv_lambdaLog_eq {τ : ℂ} (hτ : 0 < τ.im) :
    deriv lambdaLog τ = deriv modularLambda τ / modularLambda τ := by
  have hne := modularLambda_ne_zero_of_im_pos hτ
  have h1 : HasDerivAt (fun z => Complex.exp (lambdaLog z))
      (Complex.exp (lambdaLog τ) * deriv lambdaLog τ) τ := (hasDerivAt_lambdaLog hτ).cexp
  have hev : (fun z => Complex.exp (lambdaLog z)) =ᶠ[𝓝 τ] modularLambda := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hτ] with z hz
    exact exp_lambdaLog hz
  have h2 := h1.congr_of_eventuallyEq hev.symm
  rw [h2.deriv, exp_lambdaLog hτ]
  field_simp

theorem re_lambdaLog_eq {τ : ℂ} (hτ : 0 < τ.im) :
    (lambdaLog τ).re = Real.log ‖modularLambda τ‖ := by
  rw [← exp_lambdaLog hτ, Complex.norm_exp, Real.log_exp]

theorem lintegral_Ioi_log_div (G : ℝ → ℝ) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (G (Real.log r) / r) = ∫⁻ s : ℝ, ENNReal.ofReal (G s) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := univ) (f := Real.exp)
    (f' := Real.exp) MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (fun r => ENNReal.ofReal (G (Real.log r) / r))
  rw [image_univ, Real.range_exp, Measure.restrict_univ] at h
  rw [h]
  refine lintegral_congr fun s => ?_
  rw [abs_of_pos (Real.exp_pos s), Real.log_exp, ← ENNReal.ofReal_mul (Real.exp_pos s).le]
  congr 1
  field_simp

/-- `∫_ℂ G(log|z|)/|z|² dA = 2π ∫_ℝ G`. -/
theorem lintegral_log_norm_div_sq {G : ℝ → ℝ} (hG : Measurable G) :
    ∫⁻ z : ℂ, ENNReal.ofReal (G (Real.log ‖z‖) / ‖z‖ ^ 2) =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ s : ℝ, ENNReal.ofReal (G s) := by
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have hpt : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 • ENNReal.ofReal
        (G (Real.log ‖(Complex.polarCoord.symm p)‖) / ‖Complex.polarCoord.symm p‖ ^ 2) =
      ENNReal.ofReal (G (Real.log p.1) / p.1) * 1 := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hr' : (0 : ℝ) < r := hr
    rw [Complex.norm_polarCoord_symm, abs_of_pos hr', smul_eq_mul, ← ENNReal.ofReal_mul hr'.le,
      mul_one]
    congr 1
    field_simp
  rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hpt,
    Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hFm : Measurable fun r : ℝ => ENNReal.ofReal (G (Real.log r) / r) :=
    ((hG.comp Real.measurable_log).div measurable_id).ennreal_ofReal
  rw [lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal (G (Real.log r) / r))
    (g := fun _ : ℝ => (1 : ENNReal)) hFm.aemeasurable aemeasurable_const, lintegral_const,
    Measure.restrict_apply_univ, Real.volume_Ioo, one_mul, lintegral_Ioi_log_div, mul_comm,
    show Real.pi - -Real.pi = 2 * Real.pi by ring]

theorem det_restrictScalars_smulRight (c : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ : ℂ →L[ℝ] ℂ).det =
      Complex.normSq c := by
  have : (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ : ℂ →L[ℝ] ℂ) :
      ℂ →ₗ[ℝ] ℂ) = ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c : ℂ →ₗ[ℂ] ℂ).restrictScalars ℝ) :=
    rfl
  show LinearMap.det _ = _
  rw [this, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, LinearMap.det_ring]
  simp

/-- **The Dirichlet density of `L` integrates to at most `2π ∫ G` over an injectivity set of `λ`.** -/
theorem lintegral_dirichletDensity_le {D : Set ℂ} (hDm : MeasurableSet D)
    (hDH : D ⊆ {τ | 0 < τ.im}) (hinj : InjOn modularLambda D) {G : ℝ → ℝ} (hG : Measurable G) :
    ∫⁻ τ in D, ENNReal.ofReal (‖deriv lambdaLog τ‖ ^ 2 * G (lambdaLog τ).re) ≤
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ s : ℝ, ENNReal.ofReal (G s) := by
  have hder : ∀ τ ∈ D, HasFDerivWithinAt modularLambda
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv modularLambda τ)).restrictScalars ℝ)
      D τ := fun τ hτ =>
    ((differentiableAt_modularLambda_of_im_pos (hDH hτ)).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hDm hder hinj
    (fun z => ENNReal.ofReal (G (Real.log ‖z‖) / ‖z‖ ^ 2))
  calc ∫⁻ τ in D, ENNReal.ofReal (‖deriv lambdaLog τ‖ ^ 2 * G (lambdaLog τ).re)
      = ∫⁻ τ in D, ENNReal.ofReal |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
          (deriv modularLambda τ)).restrictScalars ℝ : ℂ →L[ℝ] ℂ).det| *
          ENNReal.ofReal (G (Real.log ‖modularLambda τ‖) / ‖modularLambda τ‖ ^ 2) := by
        refine setLIntegral_congr_fun hDm fun τ hτ => ?_
        have hτ' : 0 < τ.im := hDH hτ
        have hne := norm_pos_iff.2 (modularLambda_ne_zero_of_im_pos hτ')
        rw [det_restrictScalars_smulRight, deriv_lambdaLog_eq hτ', re_lambdaLog_eq hτ',
          ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_nonneg (Complex.normSq_nonneg _),
          Complex.normSq_eq_norm_sq, norm_div]
        congr 1
        field_simp
    _ = ∫⁻ z in modularLambda '' D, ENNReal.ofReal (G (Real.log ‖z‖) / ‖z‖ ^ 2) := hcv.symm
    _ ≤ ∫⁻ z : ℂ, ENNReal.ofReal (G (Real.log ‖z‖) / ‖z‖ ^ 2) := setLIntegral_le_lintegral _ _
    _ = _ := lintegral_log_norm_div_sq hG

/-- **The Dirichlet energy of the `λ`-test function** over an injectivity set `D` of `λ`:
`∫_D (|∂ₓf|² + |∂ᵧf|²) dx dy ≤ 2π ∫_ℝ (κ'² + κ²/N²)`. -/
theorem lintegral_norm_sq_fderiv_lambdaTest_le {κ : ℝ → ℝ} (hκ : Differentiable ℝ κ) (N : ℕ)
    {D : Set ℂ} (hDm : MeasurableSet D) (hDH : D ⊆ {τ | 0 < τ.im})
    (hinj : InjOn modularLambda D) :
    ∫⁻ τ in D, ENNReal.ofReal (‖fderiv ℝ (lambdaTest κ N) τ 1‖ ^ 2 +
        ‖fderiv ℝ (lambdaTest κ N) τ Complex.I‖ ^ 2) ≤
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ s : ℝ, ENNReal.ofReal (deriv κ s ^ 2 + κ s ^ 2 / (N : ℝ) ^ 2) := by
  have hGm : Measurable fun s : ℝ => deriv κ s ^ 2 + κ s ^ 2 / (N : ℝ) ^ 2 :=
    ((measurable_deriv κ).pow_const 2).add ((hκ.continuous.measurable.pow_const 2).div_const _)
  refine le_trans (le_of_eq (setLIntegral_congr_fun hDm fun τ hτ => ?_))
    (lintegral_dirichletDensity_le hDm hDH hinj hGm)
  rw [norm_sq_fderiv_lambdaTest κ N (hDH hτ) (hκ _)]

end

end GaloisForLFunctions.RHTower.ModularLambdaWinding
