import GaloisForLFunctions.HTGeometry.KleinGordonClassical

/-!
# The weighted frequency measure

The evolution with a potential is solved on the frequency side, in the space of densities integrable
against the weight `⟨ξ⟩ᵏ`. This file introduces that measure and proves the one inequality the whole
theory rests on:

`⟨ξ⟩ ≤ √2 ⟨ξ - η⟩ ⟨η⟩`,

Peetre's inequality. It says the weight is *submultiplicative up to a constant* along the
convolution variable, which is what makes the weighted `L¹` space an algebra under convolution — and
therefore what makes multiplication by a potential a bounded operator.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## Peetre's inequality -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The squared form of Peetre's inequality. -/
theorem kgFreq_sq_le_peetre (ξ η : E) :
    kgFreq ξ ^ 2 ≤ 2 * (kgFreq (ξ - η) ^ 2 * kgFreq η ^ 2) := by
  rw [kgFreq_sq, kgFreq_sq, kgFreq_sq]
  have htri : ‖ξ‖ ≤ ‖ξ - η‖ + ‖η‖ := by
    have h : ξ = (ξ - η) + η := by abel
    calc ‖ξ‖ = ‖(ξ - η) + η‖ := by rw [← h]
      _ ≤ ‖ξ - η‖ + ‖η‖ := norm_add_le _ _
  have h1 : (0 : ℝ) ≤ ‖ξ - η‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖η‖ := norm_nonneg _
  have h3 : (0 : ℝ) ≤ ‖ξ‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖ξ - η‖ - ‖η‖), sq_nonneg (‖ξ - η‖ * ‖η‖), sq_nonneg (‖ξ‖ - ‖ξ - η‖ - ‖η‖)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Peetre's inequality.** -/
theorem kgFreq_le_peetre (ξ η : E) :
    kgFreq ξ ≤ Real.sqrt 2 * (kgFreq (ξ - η) * kgFreq η) := by
  have h := kgFreq_sq_le_peetre ξ η
  have hr : (0 : ℝ) ≤ Real.sqrt 2 * (kgFreq (ξ - η) * kgFreq η) := by
    have := (kgFreq_pos (ξ - η)).le
    have := (kgFreq_pos η).le
    positivity
  have hsq : (Real.sqrt 2 * (kgFreq (ξ - η) * kgFreq η)) ^ 2
      = 2 * (kgFreq (ξ - η) ^ 2 * kgFreq η ^ 2) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), mul_pow]
  nlinarith [kgFreq_pos ξ, hr]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Peetre's inequality for the weight of order `k`.** -/
theorem kgFreq_pow_le_peetre (k : ℕ) (ξ η : E) :
    kgFreq ξ ^ k ≤ Real.sqrt 2 ^ k * (kgFreq (ξ - η) ^ k * kgFreq η ^ k) := by
  have hbase := kgFreq_le_peetre ξ η
  have hpow : kgFreq ξ ^ k ≤ (Real.sqrt 2 * (kgFreq (ξ - η) * kgFreq η)) ^ k :=
    pow_le_pow_left₀ (kgFreq_pos ξ).le hbase k
  calc kgFreq ξ ^ k ≤ (Real.sqrt 2 * (kgFreq (ξ - η) * kgFreq η)) ^ k := hpow
    _ = Real.sqrt 2 ^ k * (kgFreq (ξ - η) ^ k * kgFreq η ^ k) := by
        rw [mul_pow, mul_pow]

/-! ## The weighted measure -/

/-- The weight of order `k` as an extended nonnegative real. -/
noncomputable def kgWeight (k : ℕ) (ξ : E) : ℝ≥0∞ := ENNReal.ofReal (kgFreq ξ ^ k)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_kgWeight (k : ℕ) : Measurable (kgWeight (E := E) k) := by
  refine ENNReal.measurable_ofReal.comp ?_
  exact (continuous_kgFreq.pow k).measurable

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem kgWeight_lt_top (k : ℕ) (ξ : E) : kgWeight k ξ < ∞ := ENNReal.ofReal_lt_top

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem kgWeight_toReal (k : ℕ) (ξ : E) : (kgWeight k ξ).toReal = kgFreq ξ ^ k := by
  rw [kgWeight, ENNReal.toReal_ofReal (pow_nonneg (kgFreq_pos ξ).le k)]

/-- The frequency measure of order `k`: Lebesgue measure weighted by `⟨ξ⟩ᵏ`. -/
noncomputable def wienerMeasure (k : ℕ) : Measure E := (volume : Measure E).withDensity (kgWeight k)

/-- **Integrability against the weighted measure is integrability of the weighted density.** -/
theorem integrable_wienerMeasure_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (g : E → F) :
    Integrable g (wienerMeasure k) ↔ Integrable (fun ξ => kgFreq ξ ^ k • g ξ) volume := by
  rw [wienerMeasure,
    integrable_withDensity_iff_integrable_smul' (measurable_kgWeight k)
      (Filter.Eventually.of_forall fun ξ => kgWeight_lt_top k ξ)]
  refine integrable_congr (Filter.Eventually.of_forall fun ξ => ?_)
  show (kgWeight k ξ).toReal • g ξ = kgFreq ξ ^ k • g ξ
  rw [kgWeight_toReal]

theorem wienerMeasure_apply_eq_lintegral (k : ℕ) {s : Set E} (hs : MeasurableSet s) :
    wienerMeasure k s = ∫⁻ ξ in s, kgWeight k ξ := by
  rw [wienerMeasure, withDensity_apply _ hs]

end GaloisForLFunctions.HTGeometry
