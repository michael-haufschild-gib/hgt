import GaloisForLFunctions.RHTower.XiMassArchimedeanUniformBound

/-!
# Exact prime-only open core for the analytic mass trace

The completed archimedean channel is uniformly bounded on every positive complex-time vertical
line.  Combining that theorem with the unconditional Euler-contour identity shows that boundedness
of the mass trace is equivalent to boundedness of the literal von-Mangoldt bottom integral.  Thus
the remaining RH-strength assertion is exactly prime cancellation; no pole, Gamma, contour, or
summability seam remains hidden in the statement.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Complete mass-weighted von-Mangoldt integral on the legal Euler bottom line. -/
def xiMassBottomPrimeIntegral (a c : ℝ) (τ : ℂ) : ℂ :=
  ∫ x : ℝ, xiMassBottomPrimeIntegrand a c τ x

/-- Complete mass-weighted archimedean integral on the legal Euler bottom line. -/
def xiMassBottomArchIntegral (a c : ℝ) (τ : ℂ) : ℂ :=
  ∫ x : ℝ, xiMassBottomArchIntegrand a c τ x

/-- The literal source integral splits exactly into prime and Gamma channels. -/
theorem integral_xiMassBottomSourceIntegrand_eq_prime_add_arch
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    (∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x) =
      -I * xiMassBottomPrimeIntegral a c τ +
        I * xiMassBottomArchIntegral a c τ := by
  have hp := integrable_xiMassBottomPrimeIntegrand hhalf hca hτ
  have ha := integrable_xiMassBottomArchIntegrand hhalf hca hτ
  calc
    (∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x) =
        ∫ x : ℝ, (-I * xiMassBottomPrimeIntegrand a c τ x +
          I * xiMassBottomArchIntegrand a c τ x) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      exact xiMassBottomSourceIntegrand_eq a c τ x
    _ = -I * (∫ x : ℝ, xiMassBottomPrimeIntegrand a c τ x) +
        I * (∫ x : ℝ, xiMassBottomArchIntegrand a c τ x) := by
      rw [MeasureTheory.integral_add (hp.const_mul (-I)) (ha.const_mul I),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ = _ := rfl

/-- The source integral is exactly `π i` times the mass trace. -/
theorem integral_xiMassBottomSourceIntegrand_eq_pi_I_mul_trace
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    (∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x) =
      Real.pi * I *
        (xiMassFamily (show 1 / 2 ≤ a by linarith)).traceC τ := by
  have h := two_pi_I_mul_xiMassTraceC_eq_bottomEulerSource hhalf hca hτ
  have h' : (2 : ℂ) * (Real.pi * I *
      (xiMassFamily (show 1 / 2 ≤ a by linarith)).traceC τ) =
      (2 : ℂ) * (∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x) := by
    calc
      _ = 2 * Real.pi * I *
          (xiMassFamily (show 1 / 2 ≤ a by linarith)).traceC τ := by ring
      _ = 2 * (∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x) := h
  exact (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h').symm

/-- Prime channel recovered algebraically from complete source and harmless Gamma channel. -/
theorem xiMassBottomPrimeIntegral_eq_I_mul_source_add_arch
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    xiMassBottomPrimeIntegral a c τ =
      I * (∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x) +
        xiMassBottomArchIntegral a c τ := by
  rw [integral_xiMassBottomSourceIntegrand_eq_prime_add_arch hhalf hca hτ]
  symm
  calc
    I * (-I * xiMassBottomPrimeIntegral a c τ +
        I * xiMassBottomArchIntegral a c τ) +
        xiMassBottomArchIntegral a c τ =
      (-I * I) * xiMassBottomPrimeIntegral a c τ +
        (I * I) * xiMassBottomArchIntegral a c τ +
          xiMassBottomArchIntegral a c τ := by ring
    _ = xiMassBottomPrimeIntegral a c τ := by
      rw [neg_mul, Complex.I_mul_I]
      ring

/-- Boundedness of the literal von-Mangoldt integral on one complex-time vertical line. -/
def XiMassBottomPrimeLineBound (a c σ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ,
    ‖xiMassBottomPrimeIntegral a c ((σ : ℂ) + u * I)‖ ≤ C

/-- Boundedness of the mass trace on one complex-time vertical line. -/
def XiMassTraceLineBound (a σ : ℝ) (ha : 1 / 2 ≤ a) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ,
    ‖(xiMassFamily ha).traceC ((σ : ℂ) + u * I)‖ ≤ C

/-- Once the Gamma contour is discharged, trace boundedness is exactly prime boundedness. -/
theorem xiMassBottomPrimeLineBound_iff_xiMassTraceLineBound
    {a c σ : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hσ : 0 < σ) :
    XiMassBottomPrimeLineBound a c σ ↔
      XiMassTraceLineBound a σ (show 1 / 2 ≤ a by linarith) := by
  have haHalf : 1 / 2 ≤ a := by linarith
  let B : ℝ := xiMassBottomArchUniformBound a σ
  have hB : 0 ≤ B := xiMassBottomArchUniformBound_nonneg
    (show 0 < a by linarith) hσ
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨‖(2 * Real.pi * I : ℂ)⁻¹ * 2‖ * (C + B), fun u => ?_⟩
    let τ : ℂ := (σ : ℂ) + u * I
    have hτ : 0 < τ.re := by dsimp only [τ]; simp [Complex.mul_re]; exact hσ
    have hsource : ‖∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x‖ ≤ C + B := by
      rw [integral_xiMassBottomSourceIntegrand_eq_prime_add_arch hhalf hca hτ]
      calc
        ‖-I * xiMassBottomPrimeIntegral a c τ +
            I * xiMassBottomArchIntegral a c τ‖ ≤
          ‖-I * xiMassBottomPrimeIntegral a c τ‖ +
            ‖I * xiMassBottomArchIntegral a c τ‖ := norm_add_le _ _
        _ = ‖xiMassBottomPrimeIntegral a c τ‖ +
            ‖xiMassBottomArchIntegral a c τ‖ := by simp
        _ ≤ C + B := add_le_add (hC u)
          (norm_integral_xiMassBottomArchIntegrand_le_uniform hhalf hca hσ)
    rw [xiMassTraceC_eq_normalizedBottomEulerContour hhalf hca hτ,
      normalizedXiMassBottomEulerContour]
    rw [show (2 * Real.pi * I : ℂ)⁻¹ *
        (2 * (∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x)) =
        ((2 * Real.pi * I : ℂ)⁻¹ * 2) *
          (∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x) by ring,
      norm_mul]
    exact mul_le_mul_of_nonneg_left hsource (norm_nonneg _)
  · rintro ⟨C, hC⟩
    refine ⟨‖(Real.pi : ℂ) * I‖ * C + B, fun u => ?_⟩
    let τ : ℂ := (σ : ℂ) + u * I
    have hτ : 0 < τ.re := by dsimp only [τ]; simp [Complex.mul_re]; exact hσ
    rw [xiMassBottomPrimeIntegral_eq_I_mul_source_add_arch hhalf hca hτ]
    calc
      ‖I * (∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x) +
          xiMassBottomArchIntegral a c τ‖ ≤
        ‖I * (∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x)‖ +
          ‖xiMassBottomArchIntegral a c τ‖ := norm_add_le _ _
      _ = ‖∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x‖ +
          ‖xiMassBottomArchIntegral a c τ‖ := by simp
      _ ≤ ‖(Real.pi : ℂ) * I‖ * C + B := by
        apply add_le_add
        · rw [integral_xiMassBottomSourceIntegrand_eq_pi_I_mul_trace hhalf hca hτ,
            norm_mul]
          exact mul_le_mul_of_nonneg_left (hC u) (norm_nonneg _)
        · exact norm_integral_xiMassBottomArchIntegrand_le_uniform hhalf hca hσ

/-- Exact prime-only RH criterion.  The remaining open theorem has no auxiliary analytic terms. -/
theorem riemannHypothesis_iff_exists_xiMassBottomPrime_line_bound
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) :
    RiemannHypothesis ↔
      ∃ σ : ℝ, 0 < σ ∧ XiMassBottomPrimeLineBound a c σ := by
  have haHalf : 1 / 2 ≤ a := by linarith
  constructor
  · intro hRH
    obtain ⟨σ, C, hσ, htrace⟩ :=
      (riemannHypothesis_iff_exists_xiMassTrace_line_bound haHalf).mp hRH
    have htraceBound : XiMassTraceLineBound a σ haHalf := ⟨C, htrace⟩
    exact ⟨σ, hσ,
      (xiMassBottomPrimeLineBound_iff_xiMassTraceLineBound hhalf hca hσ).mpr
        htraceBound⟩
  · rintro ⟨σ, hσ, hprime⟩
    obtain ⟨C, htrace⟩ :=
      (xiMassBottomPrimeLineBound_iff_xiMassTraceLineBound hhalf hca hσ).mp hprime
    exact riemannHypothesis_of_xiMassTrace_line_bound haHalf hσ htrace

/-- The complete prime integral is independent of the chosen legal Euler contour depth. -/
theorem xiMassBottomPrimeIntegral_depth_independent
    {a c d : ℝ} (hcHalf : 1 / 2 < c) (hca : c < a)
    (hdHalf : 1 / 2 < d) (hda : d < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    xiMassBottomPrimeIntegral a c τ = xiMassBottomPrimeIntegral a d τ := by
  rw [xiMassBottomPrimeIntegral_eq_I_mul_source_add_arch hcHalf hca hτ,
    xiMassBottomPrimeIntegral_eq_I_mul_source_add_arch hdHalf hda hτ,
    integral_xiMassBottomSourceIntegrand_eq_pi_I_mul_trace hcHalf hca hτ,
    integral_xiMassBottomSourceIntegrand_eq_pi_I_mul_trace hdHalf hda hτ]
  unfold xiMassBottomArchIntegral
  rw [integral_xiMassBottomArch_eq_centered_add_residue hcHalf hca hτ,
    integral_xiMassBottomArch_eq_centered_add_residue hdHalf hda hτ]

theorem xiMassBottomPrimeLineBound_depth_independent
    {a c d σ : ℝ} (hcHalf : 1 / 2 < c) (hca : c < a)
    (hdHalf : 1 / 2 < d) (hda : d < a) (hσ : 0 < σ) :
    XiMassBottomPrimeLineBound a c σ ↔ XiMassBottomPrimeLineBound a d σ := by
  constructor <;> rintro ⟨C, hC⟩ <;> refine ⟨C, fun u => ?_⟩
  · have hτ : 0 < ((σ : ℂ) + u * I).re := by
      simp [Complex.mul_re]
      exact hσ
    rw [← xiMassBottomPrimeIntegral_depth_independent hcHalf hca hdHalf hda hτ]
    exact hC u
  · have hτ : 0 < ((σ : ℂ) + u * I).re := by
      simp [Complex.mul_re]
      exact hσ
    rw [xiMassBottomPrimeIntegral_depth_independent hcHalf hca hdHalf hda hτ]
    exact hC u

/-- Under RH every mass frequency is real. -/
theorem xiMassFamily_pt_im_eq_zero_of_riemannHypothesis
    {a : ℝ} (ha : 1 / 2 ≤ a) (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    ((xiMassFamily ha).pt q).im = 0 := by
  have hpos := xiMassArg_re_pos ha q
  change (HTGeometry.csqrt (xiMassArg a q)).im = 0
  rw [HTGeometry.csqrt_im]
  apply (HTGeometry.csqrtIm_eq_zero_iff hpos).mpr
  rw [xiMassArg_im, xiPoissonPoint_im_eq_zero_of_riemannHypothesis hRH q]
  ring

/-- RH bounds every positive vertical line, not only one existentially selected line. -/
theorem xiMassTraceLineBound_of_riemannHypothesis
    {a σ : ℝ} (ha : 1 / 2 ≤ a) (hσ : 0 < σ) (hRH : RiemannHypothesis) :
    XiMassTraceLineBound a σ ha := by
  refine ⟨(xiMassFamily ha).traceReal σ, fun u => ?_⟩
  have hτ : 0 < (((σ : ℂ) + u * I)).re := by
    simp [Complex.mul_re]
    exact hσ
  simpa [Complex.mul_re] using
    ((xiMassFamily ha).norm_traceC_le_of_im_eq_zero
      (xiMassFamily_pt_im_eq_zero_of_riemannHypothesis ha hRH) hτ)

/-- Sharp fixed-line formulation: for every `σ>0`, prime boundedness is already equivalent to RH. -/
theorem riemannHypothesis_iff_xiMassBottomPrimeLineBound
    {a c σ : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hσ : 0 < σ) :
    RiemannHypothesis ↔ XiMassBottomPrimeLineBound a c σ := by
  have haHalf : 1 / 2 ≤ a := by linarith
  constructor
  · intro hRH
    exact (xiMassBottomPrimeLineBound_iff_xiMassTraceLineBound hhalf hca hσ).mpr
      (xiMassTraceLineBound_of_riemannHypothesis haHalf hσ hRH)
  · intro hprime
    obtain ⟨C, htrace⟩ :=
      (xiMassBottomPrimeLineBound_iff_xiMassTraceLineBound hhalf hca hσ).mp hprime
    exact riemannHypothesis_of_xiMassTrace_line_bound haHalf hσ htrace

/-- Every legal choice of mass, depth, and positive line defines the same RH-strength proposition. -/
theorem xiMassBottomPrimeLineBound_universal
    {a₁ c₁ σ₁ a₂ c₂ σ₂ : ℝ}
    (hc₁ : 1 / 2 < c₁) (hca₁ : c₁ < a₁) (hσ₁ : 0 < σ₁)
    (hc₂ : 1 / 2 < c₂) (hca₂ : c₂ < a₂) (hσ₂ : 0 < σ₂) :
    XiMassBottomPrimeLineBound a₁ c₁ σ₁ ↔
      XiMassBottomPrimeLineBound a₂ c₂ σ₂ := by
  rw [← riemannHypothesis_iff_xiMassBottomPrimeLineBound hc₁ hca₁ hσ₁,
    ← riemannHypothesis_iff_xiMassBottomPrimeLineBound hc₂ hca₂ hσ₂]

end

end RHTower
