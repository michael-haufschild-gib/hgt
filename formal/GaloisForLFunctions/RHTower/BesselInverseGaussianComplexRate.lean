import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCauchyPowerFourierBessel

/-!
# The inverse-Gaussian Mellin integral with a complex rate

For `Re A > 0`, `P > 0` and every complex order `α`,

`∫_0^∞ y^{α−1} e^{−Ay − P/(Ay)} dy = 2 P^{α/2} A^{−α} K_α(2√P)`.

For real `A` this is the substitution `y = (√P/A) e^u` in the Schläfli integral of `K_α`
(`RHTower.integral_d4BMInverseGaussianMellinKernel_eq_bessel`).  Both sides are holomorphic in `A` on
the right half-plane — the integral by dominated differentiation, since
`|e^{−Ay−P/(Ay)}| = e^{−(Re A)y − P (Re A/|A|²)/y}` — and they agree on the positive reals, so the
identity theorem gives the complex case.  This is the `y`-integral in Kuznetsov's evaluation of the
pairing of two Poincaré series, where `A = 2πμ(1 − iξ)` and `AB = 4π²μν/c²`.
-/

open Complex MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.RHTower.Kuznetsov

noncomputable section

/-- The integrand `y^{α−1} e^{−Ay − P/(Ay)}`. -/
def invGaussKernel (α A : ℂ) (P : ℝ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ (α - 1) * Complex.exp (-(A * y) - P / (A * y))

/-- The real majorant `y^{σ−1} e^{−ay − b/y}`. -/
def invGaussMajorant (σ a b y : ℝ) : ℝ := y ^ (σ - 1) * Real.exp (-(a * y) - b / y)

theorem mul_sqrt_div_eq_sqrt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * Real.sqrt (b / a) = Real.sqrt (a * b) := by
  rw [← Real.sqrt_sq ha.le, ← Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
  congr 1
  field_simp

theorem div_sqrt_div_eq_sqrt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    b / Real.sqrt (b / a) = Real.sqrt (a * b) := by
  have hq : 0 < Real.sqrt (b / a) := Real.sqrt_pos.mpr (div_pos hb ha)
  rw [div_eq_iff hq.ne', ← Real.sqrt_mul (by positivity)]
  rw [show a * b * (b / a) = b ^ 2 by field_simp, Real.sqrt_sq hb.le]

/-- **The majorant is integrable** for `a, b > 0` and every real `σ`. -/
theorem integrableOn_invGaussMajorant (σ : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (invGaussMajorant σ a b) (Ioi 0) := by
  set q := Real.sqrt (b / a) with hqdef
  have hq : 0 < q := Real.sqrt_pos.mpr (div_pos hb ha)
  have himage : (fun u : ℝ => q * Real.exp u) '' univ = Ioi (0 : ℝ) := by
    ext x
    constructor
    · rintro ⟨u, -, rfl⟩
      exact mul_pos hq (Real.exp_pos u)
    · intro hx
      refine ⟨Real.log (x / q), mem_univ _, ?_⟩
      change q * Real.exp (Real.log (x / q)) = x
      rw [Real.exp_log (div_pos hx hq)]
      field_simp
  rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun u _ => ((Real.hasDerivAt_exp u).const_mul q).hasDerivWithinAt)
    (fun _ _ _ _ huv => Real.exp_injective (mul_left_cancel₀ hq.ne' huv))]
  have hr : 0 < 2 * Real.sqrt (a * b) := by positivity
  refine ((RHTower.integrable_d4BMExponentialBesselKernel hr (σ : ℂ)).norm.const_mul
    (q ^ σ)).integrableOn.congr_fun (fun u _ => ?_) MeasurableSet.univ
  dsimp only
  rw [RHTower.norm_d4BMExponentialBesselKernel, invGaussMajorant, smul_eq_mul,
    abs_of_pos (mul_pos hq (Real.exp_pos u)), Complex.ofReal_re]
  have haq : a * q = Real.sqrt (a * b) := mul_sqrt_div_eq_sqrt ha hb
  have hbq : b / q = Real.sqrt (a * b) := div_sqrt_div_eq_sqrt ha hb
  have h1 : (q * Real.exp u) ^ (σ - 1) = q ^ (σ - 1) * Real.exp ((σ - 1) * u) := by
    rw [Real.mul_rpow hq.le (Real.exp_pos u).le, ← Real.exp_mul, mul_comm u]
  have h2 : -(a * (q * Real.exp u)) - b / (q * Real.exp u) =
      -(Real.sqrt (a * b) * (Real.exp u + Real.exp (-u))) := by
    rw [← mul_assoc, haq, div_mul_eq_div_div, hbq, Real.exp_neg, div_eq_mul_inv]
    ring
  rw [h1, h2, Real.cosh_eq]
  have h3 : q ^ σ = q * q ^ (σ - 1) := by
    have := Real.rpow_add hq 1 (σ - 1)
    rwa [Real.rpow_one, show (1 : ℝ) + (σ - 1) = σ by ring] at this
  have e1 : Real.exp (-(2 * Real.sqrt (a * b)) * ((Real.exp u + Real.exp (-u)) / 2) + σ * u) =
      Real.exp u * Real.exp ((σ - 1) * u) *
        Real.exp (-(Real.sqrt (a * b) * (Real.exp u + Real.exp (-u)))) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [h3, e1]
  ring

theorem norm_invGaussKernel (α A : ℂ) (P : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖invGaussKernel α A P y‖ = invGaussMajorant α.re A.re (P * (A.re / Complex.normSq A)) y := by
  rw [invGaussKernel, invGaussMajorant, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
    Complex.norm_exp, Complex.sub_re, Complex.sub_re, Complex.one_re]
  congr 2
  have h1 : (-(A * (y : ℂ))).re = -(A.re * y) := by simp
  have h2 : ((P : ℂ) / (A * y)).re = P * (A.re / Complex.normSq A) / y := by
    rw [div_eq_mul_inv, mul_inv, ← Complex.ofReal_inv, ← mul_assoc, Complex.re_mul_ofReal,
      Complex.re_ofReal_mul, Complex.inv_re]
    field_simp
  rw [h1, h2]

/-- **The real-rate case.** -/
theorem integral_invGaussKernel_real (α : ℂ) {P a : ℝ} (hP : 0 < P) (ha : 0 < a) :
    ∫ y in Ioi (0 : ℝ), invGaussKernel α (a : ℂ) P y =
      2 * (P : ℂ) ^ (α / 2) * (a : ℂ) ^ (-α) * HTGeometry.modifiedBesselKOrder (2 * Real.sqrt P) α := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hxi : 0 < Real.sqrt (P / a) := Real.sqrt_pos.mpr (div_pos hP ha)
  have h := RHTower.integral_d4BMInverseGaussianMellinKernel_eq_bessel one_pos hsa hxi α
  have hint : ∀ y ∈ Ioi (0 : ℝ), invGaussKernel α (a : ℂ) P y =
      RHTower.d4BMInverseGaussianMellinKernel 1 (Real.sqrt a) (Real.sqrt (P / a)) α y := by
    intro y hy
    have hy0 : (y : ℝ) ≠ 0 := (ne_of_gt hy)
    rw [invGaussKernel, RHTower.d4BMInverseGaussianMellinKernel]
    congr 2
    rw [Real.sq_sqrt ha.le, Real.sq_sqrt (div_pos hP ha).le]
    push_cast
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hint, h]
  have harg : 2 * 1 * Real.sqrt a * Real.sqrt (P / a) = 2 * Real.sqrt P := by
    rw [mul_one, mul_assoc, ← Real.sqrt_mul ha.le, mul_div_cancel₀ _ ha.ne']
  rw [harg]
  have hratio : Real.sqrt (P / a) / Real.sqrt a = Real.sqrt P * a⁻¹ := by
    rw [Real.sqrt_div' _ ha.le, div_div, Real.mul_self_sqrt ha.le, div_eq_mul_inv]
  rw [hratio, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Real.sqrt_nonneg P)
    (inv_nonneg.mpr ha.le), Complex.ofReal_inv, Complex.inv_cpow _ _
    (by rw [Complex.arg_ofReal_of_nonneg ha.le]; exact Real.pi_ne_zero.symm), ← Complex.cpow_neg]
  have hsqrt : ((Real.sqrt P : ℝ) : ℂ) ^ α = (P : ℂ) ^ (α / 2) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hP.le, ← Complex.cpow_mul]
    · congr 1; push_cast; ring
    · rw [← Complex.ofReal_log hP.le]; simp [Real.pi_pos]
    · rw [← Complex.ofReal_log hP.le]; simp [Real.pi_pos.le]
  rw [hsqrt]
  ring

/-- The derivative of the integrand in the rate. -/
theorem hasDerivAt_invGaussKernel (α : ℂ) (P : ℝ) {y : ℝ} (hy : 0 < y) {A : ℂ} (hA : A ≠ 0) :
    HasDerivAt (fun A => invGaussKernel α A P y)
      (invGaussKernel α A P y * (-(y : ℂ) + P / (A ^ 2 * y))) A := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hAy : A * (y : ℂ) ≠ 0 := mul_ne_zero hA hy0
  have h1 : HasDerivAt (fun A : ℂ => A * y) y A := by
    simpa using (hasDerivAt_id A).mul_const (y : ℂ)
  have h2 : HasDerivAt (fun A : ℂ => (P : ℂ) / (A * y))
      ((0 * (A * y) - (P : ℂ) * y) / (A * y) ^ 2) A :=
    (hasDerivAt_const A (P : ℂ)).div h1 hAy
  have hinner : HasDerivAt (fun A : ℂ => -(A * y) - P / (A * y))
      (-(y : ℂ) + P / (A ^ 2 * y)) A :=
    (h1.neg.sub h2).congr_deriv (by field_simp; ring)
  unfold invGaussKernel
  exact ((hinner.cexp).const_mul ((y : ℂ) ^ (α - 1))).congr_deriv (by ring)

theorem invGaussMajorant_mono {σ a a' b b' y : ℝ} (hy : 0 < y) (ha : a' ≤ a) (hb : b' ≤ b) :
    invGaussMajorant σ a b y ≤ invGaussMajorant σ a' b' y := by
  unfold invGaussMajorant
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg hy.le _)
  have : b' / y ≤ b / y := div_le_div_of_nonneg_right hb hy.le
  nlinarith

/-- Local domination of the integrand near a point of the right half-plane. -/
theorem norm_invGaussKernel_le {α A A₀ : ℂ} {P : ℝ} (hP : 0 < P) (hA₀ : 0 < A₀.re)
    (hA : A ∈ Metric.ball A₀ (A₀.re / 2)) {y : ℝ} (hy : 0 < y) :
    ‖invGaussKernel α A P y‖ ≤
      invGaussMajorant α.re (A₀.re / 2) (P * ((A₀.re / 2) / (‖A₀‖ + A₀.re / 2) ^ 2)) y := by
  rw [norm_invGaussKernel α A P hy]
  have hdist : ‖A - A₀‖ < A₀.re / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hA
  have hre : A₀.re / 2 ≤ A.re := by
    have := Complex.abs_re_le_norm (A - A₀)
    rw [Complex.sub_re] at this
    have h1 : -(A.re - A₀.re) ≤ |A.re - A₀.re| := neg_le_abs _
    linarith
  have hnorm : ‖A‖ ≤ ‖A₀‖ + A₀.re / 2 := by
    have := norm_sub_norm_le A A₀
    linarith
  refine invGaussMajorant_mono hy hre (mul_le_mul_of_nonneg_left ?_ hP.le)
  rw [Complex.normSq_eq_norm_sq]
  have hA0 : 0 < ‖A‖ := lt_of_lt_of_le (by linarith) (le_trans hre (Complex.re_le_norm A))
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  exact mul_le_mul hre (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (by positivity) (by linarith)

/-- **The integral is holomorphic in the rate** on the right half-plane. -/
theorem hasDerivAt_integral_invGaussKernel (α : ℂ) {P : ℝ} (hP : 0 < P) {A₀ : ℂ}
    (hA₀ : 0 < A₀.re) :
    HasDerivAt (fun A => ∫ y in Ioi (0 : ℝ), invGaussKernel α A P y)
      (∫ y in Ioi (0 : ℝ), invGaussKernel α A₀ P y * (-(y : ℂ) + P / (A₀ ^ 2 * y))) A₀ := by
  set a₁ := A₀.re / 2
  set b₁ := P * (a₁ / (‖A₀‖ + a₁) ^ 2)
  have ha₁ : 0 < a₁ := by simp only [a₁]; linarith
  have hb₁ : 0 < b₁ := by
    have : 0 < ‖A₀‖ + a₁ := by positivity
    positivity
  have hball : ∀ A ∈ Metric.ball A₀ a₁, A ≠ 0 := by
    intro A hA h0
    have hdist : ‖A - A₀‖ < a₁ := by rwa [Metric.mem_ball, dist_eq_norm] at hA
    rw [h0, zero_sub, norm_neg] at hdist
    have := Complex.re_le_norm A₀
    simp only [a₁] at hdist
    linarith
  have hmeas : ∀ A : ℂ, AEStronglyMeasurable (invGaussKernel α A P) (volume.restrict (Ioi 0)) := by
    intro A
    refine (ContinuousOn.aestronglyMeasurable (fun y hy => ?_) measurableSet_Ioi)
    have hy0 : (y : ℝ) ≠ 0 := ne_of_gt hy
    unfold invGaussKernel
    refine ((Complex.continuousAt_ofReal_cpow_const y (α - 1) (Or.inr hy0)).mul ?_).continuousWithinAt
    refine Complex.continuous_exp.continuousAt.comp ?_
    by_cases hA : A = 0
    · subst hA; simp only [zero_mul, div_zero, neg_zero, sub_zero]; exact continuousAt_const
    · exact ((continuousAt_const.mul Complex.continuous_ofReal.continuousAt).neg).sub
        (continuousAt_const.div (continuousAt_const.mul Complex.continuous_ofReal.continuousAt)
          (mul_ne_zero hA (by exact_mod_cast hy0)))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun y => invGaussMajorant (α.re + 1) a₁ b₁ y +
      (P / a₁ ^ 2) * invGaussMajorant (α.re - 1) a₁ b₁ y)
    (F := fun A y => invGaussKernel α A P y)
    (F' := fun A y => invGaussKernel α A P y * (-(y : ℂ) + P / (A ^ 2 * y)))
    (Metric.ball_mem_nhds A₀ ha₁)
    (Eventually.of_forall fun A => hmeas A) ?_ ?_ ?_ ?_ ?_).2
  · exact ((integrableOn_invGaussMajorant α.re ha₁ hb₁).mono' (hmeas A₀)
      ((ae_restrict_mem measurableSet_Ioi).mono fun y hy =>
        norm_invGaussKernel_le hP hA₀ (Metric.mem_ball_self ha₁) hy))
  · refine ContinuousOn.aestronglyMeasurable (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (y : ℝ) ≠ 0 := ne_of_gt hy
    have hA₀0 : A₀ ≠ 0 := hball A₀ (Metric.mem_ball_self ha₁)
    refine ContinuousAt.continuousWithinAt ?_
    unfold invGaussKernel
    refine ((Complex.continuousAt_ofReal_cpow_const y (α - 1) (Or.inr hy0)).mul
      (Complex.continuous_exp.continuousAt.comp ?_)).mul ?_
    · exact ((continuousAt_const.mul Complex.continuous_ofReal.continuousAt).neg).sub
        (continuousAt_const.div (continuousAt_const.mul Complex.continuous_ofReal.continuousAt)
          (mul_ne_zero hA₀0 (by exact_mod_cast hy0)))
    · exact (Complex.continuous_ofReal.continuousAt.neg).add
        (continuousAt_const.div (continuousAt_const.mul Complex.continuous_ofReal.continuousAt)
          (mul_ne_zero (pow_ne_zero 2 hA₀0) (by exact_mod_cast hy0)))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy A hA
    have hy' : (0 : ℝ) < y := hy
    rw [norm_mul]
    have h1 := norm_invGaussKernel_le (α := α) hP hA₀ hA hy'
    have hre : a₁ ≤ A.re := by
      have hdist : ‖A - A₀‖ < A₀.re / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hA
      have := Complex.abs_re_le_norm (A - A₀)
      rw [Complex.sub_re] at this
      have h1 : -(A.re - A₀.re) ≤ |A.re - A₀.re| := neg_le_abs _
      simp only [a₁]; linarith
    have hA2 : a₁ ^ 2 ≤ ‖A‖ ^ 2 :=
      pow_le_pow_left₀ ha₁.le (hre.trans (Complex.re_le_norm A)) 2
    have h2 : ‖-(y : ℂ) + P / (A ^ 2 * y)‖ ≤ y + P / (a₁ ^ 2 * y) := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy']
      · rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos hP, abs_of_pos hy']
        exact div_le_div_of_nonneg_left hP.le (by positivity)
          (mul_le_mul_of_nonneg_right hA2 hy'.le)
    calc ‖invGaussKernel α A P y‖ * ‖-(y : ℂ) + P / (A ^ 2 * y)‖
        ≤ invGaussMajorant α.re a₁ b₁ y * (y + P / (a₁ ^ 2 * y)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by unfold invGaussMajorant; positivity)
      _ = invGaussMajorant (α.re + 1) a₁ b₁ y + P / a₁ ^ 2 * invGaussMajorant (α.re - 1) a₁ b₁ y := by
          unfold invGaussMajorant
          have e1 : y ^ (α.re - 1) * y = y ^ (α.re + 1 - 1) := by
            rw [show α.re + 1 - 1 = (α.re - 1) + 1 by ring, Real.rpow_add_one hy'.ne']
          have e2 : y ^ (α.re - 1) / y = y ^ (α.re - 1 - 1) :=
            (Real.rpow_sub_one hy'.ne' (α.re - 1)).symm
          rw [← e1, ← e2]
          field_simp
  · exact (integrableOn_invGaussMajorant (α.re + 1) ha₁ hb₁).add
      ((integrableOn_invGaussMajorant (α.re - 1) ha₁ hb₁).const_mul _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy A hA
    exact hasDerivAt_invGaussKernel α P hy (hball A hA)

/-- **The inverse-Gaussian Mellin integral with a complex rate.**  For `Re A > 0`, `P > 0`,
`∫_0^∞ y^{α−1} e^{−Ay − P/(Ay)} dy = 2 P^{α/2} A^{−α} K_α(2√P)`. -/
theorem integral_invGaussKernel (α : ℂ) {P : ℝ} (hP : 0 < P) {A : ℂ} (hA : 0 < A.re) :
    ∫ y in Ioi (0 : ℝ), invGaussKernel α A P y =
      2 * (P : ℂ) ^ (α / 2) * A ^ (-α) * HTGeometry.modifiedBesselKOrder (2 * Real.sqrt P) α := by
  classical
  set U : Set ℂ := {v : ℂ | 0 < v.re} with hU
  have hUopen : IsOpen U := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  set F : ℂ → ℂ := fun v => ∫ y in Ioi (0 : ℝ), invGaussKernel α v P y with hF
  set G : ℂ → ℂ := fun v => 2 * (P : ℂ) ^ (α / 2) * v ^ (-α) *
    HTGeometry.modifiedBesselKOrder (2 * Real.sqrt P) α with hG
  have hFa : AnalyticOnNhd ℂ F U := DifferentiableOn.analyticOnNhd (fun v hv =>
    (hasDerivAt_integral_invGaussKernel α hP hv).differentiableAt.differentiableWithinAt) hUopen
  have hGa : AnalyticOnNhd ℂ G U := by
    refine DifferentiableOn.analyticOnNhd (fun v hv => ?_) hUopen
    have hcp : DifferentiableAt ℂ (fun v : ℂ => v ^ (-α)) v :=
      differentiableAt_id.cpow_const (Or.inl hv)
    exact ((hcp.const_mul _).mul_const _).differentiableWithinAt
  have hone : (1 : ℂ) ∈ U := by simp [hU]
  have hreal : ∀ x : ℝ, 0 < x → F (x : ℂ) = G (x : ℂ) := fun x hx =>
    integral_invGaussKernel_real α hP hx
  have htend : Filter.Tendsto (fun n : ℕ => ((1 + 1 / (n + 1 : ℝ) : ℝ) : ℂ)) atTop
      (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hR : Filter.Tendsto (fun n : ℕ => (1 + 1 / (n + 1 : ℝ))) atTop (𝓝 ((1 : ℝ) + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at hR
      have hc := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hR
      simpa [Function.comp_def] using hc
    · filter_upwards with n
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcon
      have hcast : (1 : ℝ) + 1 / (n + 1 : ℝ) = 1 := by exact_mod_cast hcon
      have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
      linarith
  have hfreq : ∃ᶠ v in 𝓝[≠] (1 : ℂ), F v = G v := by
    refine htend.frequently (Filter.Eventually.frequently ?_)
    filter_upwards with n
    refine hreal _ ?_
    have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    linarith
  exact hFa.eqOn_of_preconnected_of_frequently_eq hGa hUconn hone hfreq hA

end

end GaloisForLFunctions.RHTower.Kuznetsov
