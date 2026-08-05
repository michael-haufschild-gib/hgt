import GaloisForLFunctions.HTGeometry.KleinGordonBandInvariance

/-!
# The frequency on a band

On a band the frequency is a bounded operator, and the whole calculus of the propagators simplifies
because every symbol identity that was blocked by an unbounded factor becomes an identity of bounded
multipliers.

This file records the eight identities the strong theory on a band needs. They are all instances of
one fact — the composition of two Fourier multipliers is the multiplier of the product of their
symbols — applied to products in which the factor `⟨ξ⟩` cancels against `⟨ξ⟩⁻¹` or is absorbed by the
indicator of the band.

The two that matter most are

* `⟨D⟩⁻¹⟨D⟩_R = P_R` — every band-limited vector carries one power of `⟨D⟩⁻¹`, so the regularity
  hypothesis of the differentiated theory is automatic on a band, and
* `sin(t⟨D⟩)P_R = (sin(t⟨D⟩)/⟨D⟩)⟨D⟩_R` — the propagator that was unbounded to differentiate is,
  on a band, the bounded one composed with the bounded frequency.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 1000000 in
/-- Composing two Fourier multipliers multiplies their symbols, read on a vector. -/
private theorem fourierMul_comp_apply {φ ψ χ : E → ℂ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hχ : Measurable χ) {C D B : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖φ ξ‖ ≤ C) (hD0 : 0 ≤ D)
    (hD : ∀ ξ, ‖ψ ξ‖ ≤ D) (hB0 : 0 ≤ B) (hB : ∀ ξ, ‖χ ξ‖ ≤ B)
    (hae : ∀ ξ, χ ξ = φ ξ * ψ ξ) (x : Lp ℂ 2 (volume : Measure E)) :
    fourierMulCLM hφ hC0 hC (fourierMulCLM hψ hD0 hD x) = fourierMulCLM hχ hB0 hB x :=
  congrArg (fun T : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) => T x)
    (fourierMulCLM_comp hφ hψ hχ hC0 hC hD0 hD hB0 hB (Filter.Eventually.of_forall hae))

/-! ## The frequency, cut to a band -/

/-- The symbol of `⟨D⟩` cut to the frequencies below `R`. -/
def kgFreqLow (R : ℝ) (ξ : E) : ℂ := ((kgFreq ξ : ℝ) : ℂ) * kgLowPass R ξ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_kgFreqLow (R : ℝ) : Measurable (kgFreqLow (E := E) R) :=
  ((Complex.continuous_ofReal.comp (continuous_kgFreq (E := E))).measurable).mul
    (measurable_kgLowPass R)

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem norm_kgFreqLow_le (R : ℝ) (ξ : E) : ‖kgFreqLow R ξ‖ ≤ Real.sqrt (1 + R ^ 2) := by
  rw [kgFreqLow, kgLowPass]
  split
  · rename_i hξ
    rw [mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (kgFreq_pos ξ), kgFreq]
    refine Real.sqrt_le_sqrt ?_
    have := norm_nonneg ξ
    nlinarith
  · simp only [mul_zero, norm_zero]
    positivity

/-- **`⟨D⟩` restricted to a band**, as a bounded operator. -/
def kgFreqLowOp (R : ℝ) : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  fourierMulCLM (measurable_kgFreqLow (E := E) R) (Real.sqrt_nonneg _) (norm_kgFreqLow_le R)

theorem norm_kgFreqLowOp_le (R : ℝ) : ‖kgFreqLowOp (E := E) R‖ ≤ Real.sqrt (1 + R ^ 2) :=
  norm_fourierMulCLM_le _ _ _

/-! ## The identities -/

/-- **Every band-limited vector carries one power of `⟨D⟩⁻¹`.** -/
theorem kgFreqInvOp_kgFreqLowOp (R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgFreqInvOp (kgFreqLowOp R x) = kgLowPassOp R x := by
  refine fourierMul_comp_apply _ _ (measurable_kgLowPass (E := E) R) _ _ _ _ zero_le_one
    (norm_kgLowPass_le R) (fun ξ => ?_) x
  have hpos := kgFreq_pos ξ
  have hne : ((kgFreq ξ : ℝ) : ℂ) ≠ 0 := by simpa using hpos.ne'
  rw [kgFreqInv, kgFreqLow]
  by_cases hξ : ‖ξ‖ ≤ R
  · rw [kgLowPass, if_pos hξ]
    push_cast
    field_simp
  · rw [kgLowPass, if_neg hξ]
    simp

theorem kgLowPassOp_kgFreqLowOp (R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgLowPassOp R (kgFreqLowOp R x) = kgFreqLowOp R x := by
  refine fourierMul_comp_apply _ _ (measurable_kgFreqLow (E := E) R) _ _ _ _
    (Real.sqrt_nonneg _) (norm_kgFreqLow_le R) (fun ξ => ?_) x
  rw [kgFreqLow, kgLowPass]
  split <;> ring

theorem kgFreqLowOp_kgLowPassOp (R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgFreqLowOp R (kgLowPassOp R x) = kgFreqLowOp R x := by
  refine fourierMul_comp_apply _ _ (measurable_kgFreqLow (E := E) R) _ _ _ _
    (Real.sqrt_nonneg _) (norm_kgFreqLow_le R) (fun ξ => ?_) x
  rw [kgFreqLow, kgLowPass]
  split <;> ring

/-- **The band-restricted frequency squares to the band-restricted `⟨D⟩²`.** -/
theorem kgFreqLowOp_kgFreqLowOp (R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgFreqLowOp R (kgFreqLowOp R x) = kgFreqSqLowOp R x := by
  refine fourierMul_comp_apply _ _ (measurable_kgFreqSqLow (E := E) R) _ _ _ _
    (by positivity) (norm_kgFreqSqLow_le R) (fun ξ => ?_) x
  rw [kgFreqLow, kgFreqSqLow, kgLowPass]
  split
  · push_cast
    ring
  · ring

/-- **On a band the sine propagator is the half-order one composed with the frequency.** -/
theorem kgSinOp_kgLowPassOp (t R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgSinOp t (kgLowPassOp R x) = kgSinFreqOp t (kgFreqLowOp R x) := by
  have hmeas : Measurable fun ξ : E => kgSinPhase t ξ * kgLowPass R ξ :=
    (measurable_kgSinPhase t).mul (measurable_kgLowPass R)
  have hbd : ∀ ξ : E, ‖kgSinPhase t ξ * kgLowPass R ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul]
    have h1 := norm_kgSinPhase_le t ξ
    have h2 := norm_kgLowPass_le R ξ
    nlinarith [norm_nonneg (kgSinPhase t ξ), norm_nonneg (kgLowPass R ξ)]
  have hL : kgSinOp (E := E) t (kgLowPassOp R x) = fourierMulCLM hmeas zero_le_one hbd x := by
    rw [kgSinOp_eq, kgLowPassOp_eq]
    exact fourierMul_comp_apply _ _ hmeas _ _ _ _ zero_le_one hbd (fun _ => rfl) x
  have hRgt : kgSinFreqOp (E := E) t (kgFreqLowOp R x) = fourierMulCLM hmeas zero_le_one hbd x := by
    rw [kgSinFreqOp_eq, kgFreqLowOp]
    refine fourierMul_comp_apply _ _ hmeas _ _ _ _ zero_le_one hbd (fun ξ => ?_) x
    have hpos := kgFreq_pos ξ
    have hne : ((kgFreq ξ : ℝ) : ℂ) ≠ 0 := by simpa using hpos.ne'
    rw [kgSinPhase, kgSinOverFreq, kgFreqLow]
    by_cases hξ : ‖ξ‖ ≤ R
    · rw [kgLowPass, if_pos hξ]
      push_cast
      field_simp
    · rw [kgLowPass, if_neg hξ]
      simp
  rw [hL, hRgt]

/-- **The band-restricted frequency commutes with the cosine propagator.** -/
theorem kgCosOp_kgFreqLowOp (t R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgCosOp t (kgFreqLowOp R x) = kgFreqLowOp R (kgCosOp t x) := by
  have hmeas : Measurable fun ξ : E => kgCosSymbol t ξ * kgFreqLow R ξ :=
    (measurable_kgCosSymbol t).mul (measurable_kgFreqLow R)
  have hbd : ∀ ξ : E, ‖kgCosSymbol t ξ * kgFreqLow R ξ‖ ≤ Real.sqrt (1 + R ^ 2) := by
    intro ξ
    rw [norm_mul]
    have h1 := norm_kgCosSymbol_le t ξ
    have h2 := norm_kgFreqLow_le R ξ
    nlinarith [norm_nonneg (kgCosSymbol t ξ), norm_nonneg (kgFreqLow R ξ),
      Real.sqrt_nonneg (1 + R ^ 2)]
  have hL : kgCosOp (E := E) t (kgFreqLowOp R x)
      = fourierMulCLM hmeas (Real.sqrt_nonneg _) hbd x := by
    rw [kgCosOp_eq, kgFreqLowOp]
    exact fourierMul_comp_apply _ _ hmeas _ _ _ _ (Real.sqrt_nonneg _) hbd (fun _ => rfl) x
  have hRgt : kgFreqLowOp (E := E) R (kgCosOp t x)
      = fourierMulCLM hmeas (Real.sqrt_nonneg _) hbd x := by
    rw [kgCosOp_eq, kgFreqLowOp]
    exact fourierMul_comp_apply _ _ hmeas _ _ _ _ (Real.sqrt_nonneg _) hbd
      (fun ξ => mul_comm _ _) x
  rw [hL, hRgt]

/-- **The band-restricted `⟨D⟩²` commutes with the cosine propagator.** -/
theorem kgFreqSqLowOp_kgCosOp (t R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgFreqSqLowOp R (kgCosOp t x) = kgCosOp t (kgFreqSqLowOp R x) := by
  have hmeas : Measurable fun ξ : E => kgFreqSqLow R ξ * kgCosSymbol t ξ :=
    (measurable_kgFreqSqLow R).mul (measurable_kgCosSymbol t)
  have hbd : ∀ ξ : E, ‖kgFreqSqLow R ξ * kgCosSymbol t ξ‖ ≤ 1 + R ^ 2 := by
    intro ξ
    rw [norm_mul]
    have h1 := norm_kgFreqSqLow_le R ξ
    have h2 := norm_kgCosSymbol_le t ξ
    nlinarith [norm_nonneg (kgFreqSqLow R ξ), norm_nonneg (kgCosSymbol t ξ)]
  have hL : kgFreqSqLowOp (E := E) R (kgCosOp t x)
      = fourierMulCLM hmeas (by positivity) hbd x := by
    rw [kgCosOp_eq, kgFreqSqLowOp]
    exact fourierMul_comp_apply _ _ hmeas _ _ _ _ (by positivity) hbd (fun _ => rfl) x
  have hRgt : kgCosOp (E := E) t (kgFreqSqLowOp R x)
      = fourierMulCLM hmeas (by positivity) hbd x := by
    rw [kgCosOp_eq, kgFreqSqLowOp]
    exact fourierMul_comp_apply _ _ hmeas _ _ _ _ (by positivity) hbd
      (fun ξ => mul_comm _ _) x
  rw [hL, hRgt]

/-- **The band-restricted `⟨D⟩²` turns the half-order propagator into the sine one.** -/
theorem kgFreqSqLowOp_kgSinFreqOp (t R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgFreqSqLowOp R (kgSinFreqOp t x) = kgSinOp t (kgFreqLowOp R x) := by
  have hmeas : Measurable fun ξ : E => kgSinPhase t ξ * kgFreqLow R ξ :=
    (measurable_kgSinPhase t).mul (measurable_kgFreqLow R)
  have hbd : ∀ ξ : E, ‖kgSinPhase t ξ * kgFreqLow R ξ‖ ≤ Real.sqrt (1 + R ^ 2) := by
    intro ξ
    rw [norm_mul]
    have h1 := norm_kgSinPhase_le t ξ
    have h2 := norm_kgFreqLow_le R ξ
    nlinarith [norm_nonneg (kgSinPhase t ξ), norm_nonneg (kgFreqLow R ξ),
      Real.sqrt_nonneg (1 + R ^ 2)]
  have hL : kgFreqSqLowOp (E := E) R (kgSinFreqOp t x)
      = fourierMulCLM hmeas (Real.sqrt_nonneg _) hbd x := by
    rw [kgSinFreqOp_eq, kgFreqSqLowOp]
    refine fourierMul_comp_apply _ _ hmeas _ _ _ _ (Real.sqrt_nonneg _) hbd (fun ξ => ?_) x
    have hpos := kgFreq_pos ξ
    have hne : ((kgFreq ξ : ℝ) : ℂ) ≠ 0 := by simpa using hpos.ne'
    rw [kgSinPhase, kgFreqLow, kgFreqSqLow, kgSinOverFreq]
    by_cases hξ : ‖ξ‖ ≤ R
    · rw [kgLowPass, if_pos hξ]
      push_cast
      field_simp
    · rw [kgLowPass, if_neg hξ]
      simp
  have hRgt : kgSinOp (E := E) t (kgFreqLowOp R x)
      = fourierMulCLM hmeas (Real.sqrt_nonneg _) hbd x := by
    rw [kgSinOp_eq, kgFreqLowOp]
    exact fourierMul_comp_apply _ _ hmeas _ _ _ _ (Real.sqrt_nonneg _) hbd (fun _ => rfl) x
  rw [hL, hRgt]

end GaloisForLFunctions.HTGeometry
