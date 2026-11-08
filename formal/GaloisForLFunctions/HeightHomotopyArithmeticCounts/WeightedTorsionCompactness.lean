import GaloisForLFunctions.HeightHomotopyArithmeticCounts.WeightedProbeInclusions
import GaloisForLFunctions.HeightHomotopyArithmeticCounts.WeightedTorsionOperators
import GaloisForLFunctions.HTGeometry.FiltrationNumberForm

/-!
# Compact self-adjoint representation of the torsion limit

The original kernel pairing factors through every smaller positive conductor
weight because the inclusion preserves arithmetic coefficients. Compactness of
that inclusion gives compactness into the continuous dual. Riesz representation
retains the original pair series and gives a compact self-adjoint Hilbert operator.
-/

noncomputable section
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts

/-- Restrict continuous functionals along the coefficient-preserving conductor inclusion. -/
def weightedProbeDualPrecomp (δ β : ℝ) (h : β ≤ δ) :
    (WeightedProbe β →L[ℝ] ℝ) →L[ℝ] (WeightedProbe δ →L[ℝ] ℝ) :=
  (ContinuousLinearMap.apply ℝ (WeightedProbe δ →L[ℝ] ℝ)
    (weightedProbeInclusion δ β h)).comp
      (ContinuousLinearMap.compL ℝ (WeightedProbe δ) (WeightedProbe β) ℝ)

/-- The actual torsion limit factors through every smaller positive conductor weight. -/
theorem spacingLimitOperator_factor (δ β : ℝ) (hδ : 0 < δ) (hβ : 0 < β) (h : β ≤ δ) :
    spacingLimitOperator δ hδ = (weightedProbeDualPrecomp δ β h).comp
      ((spacingLimitOperator β hβ).comp (weightedProbeInclusion δ β h)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change weightedKernelPairing δ spacingLimitKernel u v =
    weightedKernelPairing β spacingLimitKernel
      (weightedProbeInclusion δ β h u) (weightedProbeInclusion δ β h v)
  unfold weightedKernelPairing
  rw [weightedProbeInclusion_coefficients,weightedProbeInclusion_coefficients]

/-- Every positive conductor weight makes the original torsion limit compact into the dual. -/
theorem spacingLimitOperator_compact (δ : ℝ) (hδ : 0 < δ) :
    IsCompactOperator (spacingLimitOperator δ hδ) := by
  have hβ : 0 < δ/2 := half_pos hδ
  have h : δ/2 < δ := half_lt_self hδ
  rw [spacingLimitOperator_factor δ (δ/2) hδ hβ h.le]
  exact ((weightedProbeInclusion_compact δ (δ/2) h).clm_comp
    (spacingLimitOperator (δ/2) hβ)).clm_comp (weightedProbeDualPrecomp δ (δ/2) h.le)

/-- The Hilbert operator representing the original arithmetic torsion-limit pairing. -/
def spacingLimitHilbertOperator (δ : ℝ) (hδ : 0 < δ) : WeightedProbe δ →L[ℝ] WeightedProbe δ :=
  HTGeometry.formRiesz (spacingLimitOperator δ hδ)

/-- Riesz representation retains the original absolutely convergent arithmetic series. -/
theorem spacingLimitHilbertOperator_inner (δ : ℝ) (hδ : 0 < δ) (u v : WeightedProbe δ) :
    inner ℝ (spacingLimitHilbertOperator δ hδ u) v = weightedKernelPairing δ spacingLimitKernel u v :=
  HTGeometry.inner_formRiesz (spacingLimitOperator δ hδ) u v

/-- The actual Hilbert representative is self-adjoint. -/
theorem spacingLimitHilbertOperator_selfAdjoint (δ : ℝ) (hδ : 0 < δ) :
    IsSelfAdjoint (spacingLimitHilbertOperator δ hδ) :=
  HTGeometry.isSelfAdjoint_formRiesz (spacingLimitOperator_comm δ hδ)

/-- The Hilbert representative is compact for every positive conductor exponent. -/
theorem spacingLimitHilbertOperator_compact (δ : ℝ) (hδ : 0 < δ) :
    IsCompactOperator (spacingLimitHilbertOperator δ hδ) :=
  (spacingLimitOperator_compact δ hδ).continuous_comp
    (InnerProductSpace.toDual ℝ (WeightedProbe δ)).symm.continuous

#print axioms spacingLimitHilbertOperator_inner
#print axioms spacingLimitHilbertOperator_selfAdjoint
#print axioms spacingLimitHilbertOperator_compact
#print axioms spacingLimitOperator_factor
#print axioms spacingLimitOperator_compact
end GaloisForLFunctions.HeightHomotopyArithmeticCounts
