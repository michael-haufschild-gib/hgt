import GaloisForLFunctions.HTGeometry.CharacteristicEquilibriumDefect
import GaloisForLFunctions.HTGeometry.JuliaDefectEquilibriumPositiveDefinite

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

/-- **Universal anchored equilibrium-capacity law.**  Let `μ` be any probability law whose
second moment is the positive number `m`.  For every finite packet, correlation with the origin
through the normalized characteristic defect is bounded in square by the complete coherent Gram
energy. -/
theorem normalizedCharacteristicDefect_anchorCorrelation_sq_le_gramEnergy
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {m : ℝ} (hm : 0 < m)
    (hsq : Integrable (fun x : ℝ => x ^ 2) μ)
    (hmoment : ∫ x : ℝ, x ^ 2 ∂μ = m)
    {N : ℕ} (t b : Fin N → ℝ) :
    (∑ i, b i * normalizedCharacteristicDefect μ m (t i)) ^ 2 ≤
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
    (∑ i, b i * juliaDefectAttenuationKernel (t i)) ^ 2 ≤
      ∑ i, ∑ j,
        b i * juliaDefectAttenuationKernel (t j - t i) * b j := by
  simpa only [normalizedCharacteristicDefect_juliaCompressionEquilibriumProbabilityMeasure]
    using
      (normalizedCharacteristicDefect_anchorCorrelation_sq_le_gramEnergy
        (juliaCompressionEquilibriumProbabilityMeasure : Measure ℝ)
        (m := (3 / 2 : ℝ)) (by norm_num)
        integrable_sq_juliaCompressionEquilibriumProbabilityMeasure
        integral_sq_juliaCompressionEquilibriumProbabilityMeasure t b)

end

end HTGeometry
