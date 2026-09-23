import GaloisForLFunctions.HTGeometry.CharacteristicEquilibriumDefect
import GaloisForLFunctions.HTGeometry.JuliaDefectEquilibriumPositiveDefinite
import GaloisForLFunctions.HTGeometry.PositiveDefinitePacketCauchy

/-!
# Characteristic-defect Gram capacity

The normalized second-order defect of every probability characteristic function with finite
positive second moment is not only positive definite: its correlation with the origin is bounded
by its full coherent finite-packet energy.  This combines the equilibrium-clock realization with
the anchored Schur-complement law and specializes to the Julia center-mixed kernel.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HTGeometry

noncomputable section

open GaloisForLFunctions.HTGeometry

@[simp] theorem normalizedCharacteristicDefect_zero
    (μ : Measure ℝ) (m : ℝ) :
    normalizedCharacteristicDefect μ m 0 = 1 := by
  simp [normalizedCharacteristicDefect]

theorem normalizedCharacteristicDefect_neg
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (m y : ℝ) :
    normalizedCharacteristicDefect μ m (-y) =
      normalizedCharacteristicDefect μ m y := by
  by_cases hy : y = 0
  · subst y
    simp
  · rw [normalizedCharacteristicDefect, normalizedCharacteristicDefect,
      if_neg (neg_ne_zero.mpr hy), if_neg hy, charFun_neg]
    simp only [Complex.conj_re, neg_sq]

/-- A normalized characteristic defect is nonnegative: it is the expectation of a sinc-square
under the square-biased source law. -/
theorem normalizedCharacteristicDefect_nonneg
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {m : ℝ} (hm : 0 < m)
    (hsq : Integrable (fun x : ℝ => x ^ (2 : ℕ)) μ)
    (hmoment : ∫ x : ℝ, x ^ (2 : ℕ) ∂μ = m) (y : ℝ) :
    0 ≤ normalizedCharacteristicDefect μ m y := by
  rw [← integral_squareBias_sinc_sq_eq_normalizedCharacteristicDefect
    μ hm hsq hmoment y]
  exact integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun x =>
      mul_nonneg (div_nonneg (sq_nonneg x) hm.le) (sq_nonneg _))

/-- A normalized characteristic defect is at most one: its equilibrium-clock realization is a
probability characteristic function. -/
theorem normalizedCharacteristicDefect_le_one
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {m : ℝ} (hm : 0 < m)
    (hsq : Integrable (fun x : ℝ => x ^ (2 : ℕ)) μ)
    (hmoment : ∫ x : ℝ, x ^ (2 : ℕ) ∂μ = m) (y : ℝ) :
    normalizedCharacteristicDefect μ m y ≤ 1 := by
  have hnorm := norm_charFun_le_one
    (μ := (equilibriumClockProbabilityMeasure μ hm hsq hmoment : Measure ℝ)) y
  rw [charFun_equilibriumClockProbabilityMeasure μ hm hsq hmoment,
    Complex.norm_real, Real.norm_eq_abs] at hnorm
  exact (le_abs_self _).trans hnorm

/-- **Equilibrium two-packet capacity law.**  Mixed correlation between any two finite packets
for a normalized characteristic defect is controlled by the product of their coherent energies. -/
theorem normalizedCharacteristicDefect_packetCross_sq_le_energy_mul_energy
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {m : ℝ} (hm : 0 < m)
    (hsq : Integrable (fun x : ℝ => x ^ (2 : ℕ)) μ)
    (hmoment : ∫ x : ℝ, x ^ (2 : ℕ) ∂μ = m)
    {N M : ℕ} (s a : Fin N → ℝ) (t b : Fin M → ℝ) :
    (∑ i, ∑ j,
        a i * normalizedCharacteristicDefect μ m (t j - s i) * b j) ^ (2 : ℕ) ≤
      (∑ i, ∑ j,
          a i * normalizedCharacteristicDefect μ m (s j - s i) * a j) *
        ∑ i, ∑ j,
          b i * normalizedCharacteristicDefect μ m (t j - t i) * b j := by
  simpa only [GaloisForLFunctions.HTGeometry.realKernelPacketCross,
    GaloisForLFunctions.HTGeometry.realKernelPacketEnergy] using
      (GaloisForLFunctions.HTGeometry.realKernelPacketCross_sq_le_energy_mul_energy_of_positiveDefinite
          (normalizedCharacteristicDefect μ m)
          (positiveDefiniteOnReal_normalizedCharacteristicDefect μ hm hsq hmoment)
          (normalizedCharacteristicDefect_neg μ m) s a t b)

/-- **Universal anchored equilibrium-capacity law.**  Let `μ` be any probability law whose
second moment is the positive number `m`.  For every finite packet, correlation with the origin
through the normalized characteristic defect is bounded in square by the complete coherent Gram
energy. -/
theorem normalizedCharacteristicDefect_anchorCorrelation_sq_le_gramEnergy
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {m : ℝ} (hm : 0 < m)
    (hsq : Integrable (fun x : ℝ => x ^ (2 : ℕ)) μ)
    (hmoment : ∫ x : ℝ, x ^ (2 : ℕ) ∂μ = m)
    {N : ℕ} (t b : Fin N → ℝ) :
    (∑ i, b i * normalizedCharacteristicDefect μ m (t i)) ^ (2 : ℕ) ≤
      ∑ i, ∑ j,
        b i * normalizedCharacteristicDefect μ m (t j - t i) * b j := by
  exact anchorCorrelation_sq_le_gramEnergy_of_positiveDefinite
    (normalizedCharacteristicDefect μ m)
    (positiveDefiniteOnReal_normalizedCharacteristicDefect μ hm hsq hmoment)
    (normalizedCharacteristicDefect_zero μ m)
    (normalizedCharacteristicDefect_neg μ m) t b

/-- Julia center-mixed capacity is the source-specific shadow of the universal equilibrium law. -/
theorem juliaDefectAttenuationKernel_anchorCorrelation_sq_le_gramEnergy
    {N : ℕ} (t b : Fin N → ℝ) :
    (∑ i, b i * juliaDefectAttenuationKernel (t i)) ^ (2 : ℕ) ≤
      ∑ i, ∑ j,
        b i * juliaDefectAttenuationKernel (t j - t i) * b j := by
  simpa only [normalizedCharacteristicDefect_juliaCompressionEquilibriumProbabilityMeasure]
    using
      (normalizedCharacteristicDefect_anchorCorrelation_sq_le_gramEnergy
        (juliaCompressionEquilibriumProbabilityMeasure : Measure ℝ)
        (m := (3 / 2 : ℝ)) (by norm_num)
        integrable_sq_juliaCompressionEquilibriumProbabilityMeasure
        integral_sq_juliaCompressionEquilibriumProbabilityMeasure t b)

/-- Mixed Julia equilibrium correlation obeys the universal two-packet capacity law. -/
theorem juliaDefectAttenuationKernel_packetCross_sq_le_energy_mul_energy
    {N M : ℕ} (s a : Fin N → ℝ) (t b : Fin M → ℝ) :
    (∑ i, ∑ j,
        a i * juliaDefectAttenuationKernel (t j - s i) * b j) ^ (2 : ℕ) ≤
      (∑ i, ∑ j,
          a i * juliaDefectAttenuationKernel (s j - s i) * a j) *
        ∑ i, ∑ j,
          b i * juliaDefectAttenuationKernel (t j - t i) * b j := by
  simpa only [normalizedCharacteristicDefect_juliaCompressionEquilibriumProbabilityMeasure]
    using
      (normalizedCharacteristicDefect_packetCross_sq_le_energy_mul_energy
        (juliaCompressionEquilibriumProbabilityMeasure : Measure ℝ)
        (m := (3 / 2 : ℝ)) (by norm_num)
        integrable_sq_juliaCompressionEquilibriumProbabilityMeasure
        integral_sq_juliaCompressionEquilibriumProbabilityMeasure s a t b)

theorem juliaDefectAttenuationKernel_le_one (y : ℝ) :
    juliaDefectAttenuationKernel y ≤ 1 := by
  simpa only [normalizedCharacteristicDefect_juliaCompressionEquilibriumProbabilityMeasure]
    using
      (normalizedCharacteristicDefect_le_one
        (juliaCompressionEquilibriumProbabilityMeasure : Measure ℝ)
        (m := (3 / 2 : ℝ)) (by norm_num)
        integrable_sq_juliaCompressionEquilibriumProbabilityMeasure
        integral_sq_juliaCompressionEquilibriumProbabilityMeasure y)

end

end HTGeometry
