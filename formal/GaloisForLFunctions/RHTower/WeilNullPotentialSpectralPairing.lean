import GaloisForLFunctions.RHTower.WeilNearNullRegularRigidity
import GaloisForLFunctions.RHTower.WeilDeviationSpectralPairing

/-!
# The spectral pairing of a null potential with logarithmic coefficients

Let `u : ℕ → ℝ` with `u 0 = 0`, `|u(n)| ≤ 2 log n + A`, and let
`ψ_u(y) = Σ_n u(n)(K(y + log n) + K(y − log n))` be its null potential (`K` Riemann's
autocorrelation, `𝓕K = Ξ²`). Then `ψ_u` is continuous (`continuous_nullPotential_of_log`), and if
`−ψ_u = charFun σ` for a finite measure `σ` then for every continuous integrable `g` whose transform
decays like `(1 + |v|)^{−J}` (`nullPotential_pairing`):

`Σ_n u(n) (𝓕(Ξ²g)(log n) + 𝓕(Ξ²g)(−log n)) = −∫ g(t/2π) dσ(t)`,

provided `Σ_n |u(n)| (1 + log n)^{−J} < ∞`. No summability of `u` itself is needed: the kernel
smoothing `∫ K(v − c)|𝓕g(v)| dv ≤ C (1 + |c|)^{−J}` (`integral_riemannAutocorr_mul_le`) carries the
decay of `𝓕g` to the sample points `±log n`, by Peetre's inequality
`1 + |c| ≤ (1 + |v|)(1 + |v − c|)`.
-/

open Complex MeasureTheory Filter Topology Set FourierTransform
open scoped Real ComplexConjugate

namespace RHTower.WeilRegular

open RHTower.WeilExcess

noncomputable section

variable {u : ℕ → ℝ}

theorem continuous_nullPotential_of_log (hu0 : u 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |u n| ≤ 2 * Real.log n + A) : Continuous (nullPotential u) := by
  obtain ⟨C₁, -, hC₁⟩ := RHTower.WeilExcess.exists_riemannAutocorr_le
  rw [continuous_iff_continuousAt]
  intro y₀
  have hon : ContinuousOn (nullPotential u) (Metric.ball y₀ 1) := by
    refine continuousOn_tsum (fun n => ?_)
      ((RHTower.WeilExcess.summable_log_add_mul_inv_sq hA).mul_left
        (2 * C₁ * Real.exp (2 * (|y₀| + 1))))
      (fun n y hy => RHTower.WeilExcess.norm_potential_term_le
        RHTower.WeilExcess.riemannAutocorr_nonneg hC₁ ha hu0 hA ?_ n)
    · exact (continuous_const.mul ((RHTower.WeilExcess.continuous_riemannAutocorr.comp
        (continuous_id.add continuous_const)).add
        (RHTower.WeilExcess.continuous_riemannAutocorr.comp
          (continuous_id.sub continuous_const)))).continuousOn
    · rw [Metric.mem_ball, Real.dist_eq] at hy
      have := abs_sub_abs_le_abs_sub y y₀
      linarith
  exact hon.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))

/-! ## Kernel smoothing of polynomial decay -/

/-- Peetre's inequality: `(1 + |c|)^J ≤ (1 + |v|)^J (1 + |v − c|)^J`. -/
theorem one_add_abs_pow_le_mul (J : ℕ) (v c : ℝ) :
    (1 + |c|) ^ J ≤ (1 + |v|) ^ J * (1 + |v - c|) ^ J := by
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have h2 : |c| ≤ |v| + |v - c| := by
    have := abs_sub v (v - c)
    rwa [sub_sub_cancel] at this
  nlinarith [abs_nonneg v, abs_nonneg (v - c)]

theorem exp_neg_two_abs_mul_pow_le (J : ℕ) (w : ℝ) :
    Real.exp (-(2 * |w|)) * (1 + |w|) ^ J ≤ J.factorial * Real.exp 1 * Real.exp (-|w|) := by
  have h := Real.pow_div_factorial_le_exp (x := 1 + |w|) (by positivity) J
  have hf : (0 : ℝ) < J.factorial := by exact_mod_cast J.factorial_pos
  rw [div_le_iff₀ hf] at h
  calc Real.exp (-(2 * |w|)) * (1 + |w|) ^ J
      ≤ Real.exp (-(2 * |w|)) * (Real.exp (1 + |w|) * J.factorial) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = J.factorial * Real.exp 1 * Real.exp (-|w|) := by
        rw [show Real.exp (-(2 * |w|)) * (Real.exp (1 + |w|) * J.factorial) =
          J.factorial * (Real.exp (-(2 * |w|)) * Real.exp (1 + |w|)) by ring,
          ← Real.exp_add, show -(2 * |w|) + (1 + |w|) = 1 + -|w| by ring, Real.exp_add]
        ring

theorem integrable_exp_neg_two_abs_mul_pow (J : ℕ) :
    Integrable (fun w : ℝ => Real.exp (-(2 * |w|)) * (1 + |w|) ^ J) := by
  refine (integrable_exp_neg_abs.const_mul ((J.factorial : ℝ) * Real.exp 1)).mono'
    (by fun_prop) (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact exp_neg_two_abs_mul_pow_le J w

/-- The exponential moment `∫ e^{−2|w|}(1 + |w|)^J dw`. -/
def expMoment (J : ℕ) : ℝ := ∫ w : ℝ, Real.exp (-(2 * |w|)) * (1 + |w|) ^ J

theorem expMoment_nonneg (J : ℕ) : 0 ≤ expMoment J :=
  integral_nonneg fun w => by positivity

/-- **Kernel smoothing of polynomial decay**: if `P(v)(1 + |v|)^J ≤ C_P`, then
`∫ K(v − c) P(v) dv ≤ C₁ C_P E_J (1 + |c|)^{−J}`. -/
theorem integral_riemannAutocorr_mul_le {C₁ : ℝ}
    (hC₁ : ∀ y, riemannAutocorr y ≤ C₁ * Real.exp (-(2 * |y|))) {P : ℝ → ℝ}
    (hP0 : ∀ v, 0 ≤ P v) {J : ℕ} {CP : ℝ} (hP : ∀ v, P v * (1 + |v|) ^ J ≤ CP) (c : ℝ) :
    ∫ v, riemannAutocorr (v - c) * P v ≤ C₁ * CP * expMoment J * ((1 + |c|) ^ J)⁻¹ := by
  have hCP : 0 ≤ CP := (mul_nonneg (hP0 0) (by positivity)).trans (hP 0)
  have hC₁0 : 0 ≤ C₁ := by
    have := (riemannAutocorr_nonneg 0).trans (hC₁ 0)
    simp at this
    exact this
  have hc : 0 < (1 + |c|) ^ J := by positivity
  set M : ℝ → ℝ := fun v => C₁ * CP * ((1 + |c|) ^ J)⁻¹ *
    (Real.exp (-(2 * |v - c|)) * (1 + |v - c|) ^ J) with hM
  have hMi : Integrable M :=
    ((integrable_exp_neg_two_abs_mul_pow J).comp_sub_right c).const_mul _
  have hpt : ∀ v, riemannAutocorr (v - c) * P v ≤ M v := by
    intro v
    have hv : 0 < (1 + |v|) ^ J := by positivity
    have hPv : P v ≤ CP * ((1 + |v|) ^ J)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hv]
      exact hP v
    have hpe := one_add_abs_pow_le_mul J v c
    have hinv : ((1 + |v|) ^ J)⁻¹ ≤ (1 + |v - c|) ^ J * ((1 + |c|) ^ J)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hc, inv_mul_eq_div, div_le_iff₀ hv]
      linarith [mul_comm ((1 + |v|) ^ J) ((1 + |v - c|) ^ J)]
    calc riemannAutocorr (v - c) * P v
        ≤ (C₁ * Real.exp (-(2 * |v - c|))) * (CP * ((1 + |v - c|) ^ J * ((1 + |c|) ^ J)⁻¹)) := by
          apply mul_le_mul (hC₁ _) (hPv.trans (mul_le_mul_of_nonneg_left hinv hCP)) (hP0 v)
          positivity
      _ = M v := by rw [hM]; ring
  calc ∫ v, riemannAutocorr (v - c) * P v ≤ ∫ v, M v :=
        integral_mono_of_nonneg (Eventually.of_forall fun v =>
          mul_nonneg (riemannAutocorr_nonneg _) (hP0 v)) hMi (Eventually.of_forall hpt)
    _ = C₁ * CP * ((1 + |c|) ^ J)⁻¹ * expMoment J := by
        rw [hM, integral_const_mul]
        congr 1
        exact integral_sub_right_eq_self (fun w => Real.exp (-(2 * |w|)) * (1 + |w|) ^ J) c
    _ = C₁ * CP * expMoment J * ((1 + |c|) ^ J)⁻¹ := by ring

/-! ## The pairing -/

theorem integrable_fourier_of_decay {g : ℝ → ℂ} (hg : Integrable g) {J : ℕ} (hJ : 2 ≤ J)
    {Cg : ℝ} (hdec : ∀ v, ‖𝓕 g v‖ * (1 + |v|) ^ J ≤ Cg) : Integrable (𝓕 g) := by
  refine (integrable_inv_one_add_sq.const_mul Cg).mono'
    (continuous_fourier_integrable hg).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  have h1 : 1 + v ^ 2 ≤ (1 + |v|) ^ J := by
    calc 1 + v ^ 2 ≤ (1 + |v|) ^ 2 := by nlinarith [abs_nonneg v, sq_abs v]
      _ ≤ (1 + |v|) ^ J := pow_le_pow_right₀ (by linarith [abs_nonneg v]) hJ
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ‖𝓕 g v‖ * (1 + v ^ 2) ≤ ‖𝓕 g v‖ * (1 + |v|) ^ J :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ Cg := hdec v

/-- **The null potential paired with `𝓕(Ξ²g)` is `∫ ψ_u 𝓕g`.** -/
theorem nullPotential_pairing_eq_integral (hu0 : u 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |u n| ≤ 2 * Real.log n + A) {J : ℕ} (hJ : 2 ≤ J)
    (hsum : Summable fun n : ℕ => |u n| * ((1 + Real.log n) ^ J)⁻¹)
    {g : ℝ → ℂ} (hg : Integrable g) {Cg : ℝ} (hdec : ∀ v, ‖𝓕 g v‖ * (1 + |v|) ^ J ≤ Cg) :
    ∑' n : ℕ, (u n : ℂ) * (𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (Real.log n) +
        𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (-Real.log n)) =
      ∫ v, (nullPotential u v : ℂ) * 𝓕 g v := by
  have hFg := integrable_fourier_of_decay hg hJ hdec
  obtain ⟨C₁, hC₁0, hC₁⟩ := RHTower.WeilExcess.exists_riemannAutocorr_le
  set P : ℝ → ℝ := fun v => ‖𝓕 g v‖ with hP
  have hP0 : ∀ v, 0 ≤ P v := fun v => norm_nonneg _
  set F : ℕ → ℝ → ℂ := fun n v => (u n : ℂ) *
    (((riemannAutocorr (v - Real.log n) + riemannAutocorr (v + Real.log n) : ℝ) : ℂ) * 𝓕 g v)
    with hF
  have hKc : ∀ c : ℝ, Continuous fun v => riemannAutocorr (v - c) :=
    fun c => continuous_riemannAutocorr.comp (continuous_id.sub continuous_const)
  have hKi : ∀ c : ℝ, Integrable fun v => ((riemannAutocorr (v - c) : ℝ) : ℂ) * 𝓕 g v := by
    intro c
    refine (hFg.norm.const_mul (riemannAutocorr 0)).mono'
      (((Complex.continuous_ofReal.comp (hKc c)).mul
        (continuous_fourier_integrable hg)).aestronglyMeasurable)
      (Eventually.of_forall fun v => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (riemannAutocorr_nonneg _)]
    exact mul_le_mul_of_nonneg_right (riemannAutocorr_le_zero _) (norm_nonneg _)
  have hKPi : ∀ c : ℝ, Integrable fun v => riemannAutocorr (v - c) * P v := by
    intro c
    refine (hFg.norm.const_mul (riemannAutocorr 0)).mono'
      (((hKc c).mul (continuous_fourier_integrable hg).norm).aestronglyMeasurable)
      (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (riemannAutocorr_nonneg _) (hP0 v))]
    exact mul_le_mul_of_nonneg_right (riemannAutocorr_le_zero _) (hP0 v)
  have hFi : ∀ n, Integrable (F n) := by
    intro n
    have h := ((hKi (Real.log n)).add (hKi (-Real.log n))).const_mul (u n : ℂ)
    refine h.congr (Eventually.of_forall fun v => ?_)
    simp only [hF, Pi.add_apply, sub_neg_eq_add]; push_cast; ring
  have hterm : ∀ n : ℕ, (u n : ℂ) *
      (𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (Real.log n) +
        𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (-Real.log n)) = ∫ v, F n v := by
    intro n
    rw [fourier_riemannXi_sq_mul hg, fourier_riemannXi_sq_mul hg,
      ← integral_add (hKi _) (hKi _), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [hF, sub_neg_eq_add]; push_cast; ring
  have hnorm : ∀ n, ∫ v, ‖F n v‖ = |u n| *
      ((∫ v, riemannAutocorr (v - Real.log n) * P v) +
        ∫ v, riemannAutocorr (v - -Real.log n) * P v) := by
    intro n
    rw [← integral_add (hKPi _) (hKPi _), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [hF, hP, norm_mul, Complex.norm_real, Real.norm_eq_abs, sub_neg_eq_add]
    rw [abs_of_nonneg (add_nonneg (riemannAutocorr_nonneg _) (riemannAutocorr_nonneg _))]
    ring
  have hCg : 0 ≤ Cg := (mul_nonneg (norm_nonneg _) (by positivity)).trans (hdec 0)
  have hbound : ∀ n : ℕ, ∫ v, ‖F n v‖ ≤
      2 * (C₁ * Cg * expMoment J) * (|u n| * ((1 + Real.log n) ^ J)⁻¹) := by
    intro n
    rw [hnorm]
    have hlog : |Real.log n| = Real.log n := abs_of_nonneg (Real.log_natCast_nonneg n)
    have h1 := integral_riemannAutocorr_mul_le hC₁ hP0 hdec (Real.log n)
    have h2 := integral_riemannAutocorr_mul_le hC₁ hP0 hdec (-Real.log n)
    rw [hlog] at h1
    rw [abs_neg, hlog] at h2
    calc |u n| * ((∫ v, riemannAutocorr (v - Real.log n) * P v) +
          ∫ v, riemannAutocorr (v - -Real.log n) * P v)
        ≤ |u n| * (C₁ * Cg * expMoment J * ((1 + Real.log n) ^ J)⁻¹ +
            C₁ * Cg * expMoment J * ((1 + Real.log n) ^ J)⁻¹) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) (abs_nonneg _)
      _ = 2 * (C₁ * Cg * expMoment J) * (|u n| * ((1 + Real.log n) ^ J)⁻¹) := by ring
  have hsumnorm : Summable fun n => ∫ v, ‖F n v‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun v => norm_nonneg _) hbound
      (hsum.mul_left _)
  rw [tsum_congr hterm, integral_tsum_of_summable_integral_norm hFi hsumnorm]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [hF]
  have hs := RHTower.WeilExcess.summable_potential_term RHTower.WeilExcess.riemannAutocorr_nonneg
    hC₁ ha hu0 hA v
  unfold nullPotential
  rw [Complex.ofReal_tsum, ← tsum_mul_right]
  refine tsum_congr fun n => ?_
  rw [add_comm (riemannAutocorr (v - Real.log n))]
  push_cast; ring

/-- `∫ ψ_u 𝓕g = −∫ g(t/2π) dσ(t)` when `−ψ_u = charFun σ`. -/
theorem integral_nullPotential_mul_fourier (σ : Measure ℝ) [IsFiniteMeasure σ]
    (hσ : ∀ t, charFun σ t = ((-nullPotential u t : ℝ) : ℂ))
    {g : ℝ → ℂ} (hgc : Continuous g) (hg : Integrable g) (hFg : Integrable (𝓕 g)) :
    ∫ v, (nullPotential u v : ℂ) * 𝓕 g v = -∫ t, g (t / (2 * π)) ∂σ := by
  have hψ : ∀ v, (nullPotential u v : ℂ) = -∫ t : ℝ, Complex.exp ((v : ℂ) * t * I) ∂σ := by
    intro v
    rw [← charFun_apply_real, hσ]; push_cast; ring
  have hint : Integrable (Function.uncurry fun (v t : ℝ) => Complex.exp ((v : ℂ) * t * I) * 𝓕 g v)
      (volume.prod σ) := by
    have h1 : Integrable (fun p : ℝ × ℝ => 𝓕 g p.1 * (1 : ℂ)) (volume.prod σ) :=
      hFg.mul_prod (integrable_const (1 : ℂ))
    refine h1.norm.mono' ((Continuous.aestronglyMeasurable (by fun_prop)).mul
      (continuous_fourier_integrable hg).aestronglyMeasurable.comp_fst)
      (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, norm_mul, mul_one]
    rw [show (p.1 : ℂ) * p.2 * I = ((p.1 * p.2 : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  have hinv : ∀ t : ℝ, ∫ v : ℝ, Complex.exp ((v : ℂ) * t * I) * 𝓕 g v = g (t / (2 * π)) := by
    intro t
    have h := hg.fourierInv_fourier_eq hFg (v := t / (2 * π)) hgc.continuousAt
    rw [fourierInv_eq_integral] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    push_cast; field_simp
  calc ∫ v, (nullPotential u v : ℂ) * 𝓕 g v
      = ∫ v : ℝ, -(∫ t : ℝ, Complex.exp ((v : ℂ) * t * I) * 𝓕 g v ∂σ) := by
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        dsimp only
        rw [hψ, integral_mul_const]; ring
    _ = -∫ v : ℝ, (∫ t : ℝ, Complex.exp ((v : ℂ) * t * I) * 𝓕 g v ∂σ) := integral_neg _
    _ = -∫ t : ℝ, (∫ v : ℝ, Complex.exp ((v : ℂ) * t * I) * 𝓕 g v) ∂σ := by
        rw [integral_integral_swap hint]
    _ = -∫ t, g (t / (2 * π)) ∂σ := by
        congr 1
        exact integral_congr_ae (Eventually.of_forall hinv)

/-- **The spectral pairing of a null potential.** -/
theorem nullPotential_pairing (hu0 : u 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |u n| ≤ 2 * Real.log n + A) {J : ℕ} (hJ : 2 ≤ J)
    (hsum : Summable fun n : ℕ => |u n| * ((1 + Real.log n) ^ J)⁻¹)
    (σ : Measure ℝ) [IsFiniteMeasure σ] (hσ : ∀ t, charFun σ t = ((-nullPotential u t : ℝ) : ℂ))
    {g : ℝ → ℂ} (hgc : Continuous g) (hg : Integrable g) {Cg : ℝ}
    (hdec : ∀ v, ‖𝓕 g v‖ * (1 + |v|) ^ J ≤ Cg) :
    ∑' n : ℕ, (u n : ℂ) * (𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (Real.log n) +
        𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (-Real.log n)) = -∫ t, g (t / (2 * π)) ∂σ := by
  rw [nullPotential_pairing_eq_integral hu0 hA ha hJ hsum hg hdec,
    integral_nullPotential_mul_fourier σ hσ hgc hg (integrable_fourier_of_decay hg hJ hdec)]

end

end RHTower.WeilRegular
