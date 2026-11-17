import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeZeroPhaseSensitivity
import GaloisForLFunctions.HilbertMetric.Spectral.CompactPermutation

/-!
# Compactness detects the off-line reflection support

The actual reflection of zero coordinates is a compact perturbation of
identity exactly when only finitely many zero coordinates lie off the
critical line. This is the coordinate-permutation compactness theorem
applied to functional-equation reflection.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open ArithmeticCastelnuovoSeveri Zeta23 HilbertMetric.PermutationCompact

/-- The actual zero reflection is its coordinate permutation operator. -/
theorem zeroReflection_eq_permutationOperator :
    zeroReflection = permutationOperator (reflectEquiv zetaZeroConfig) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext z
  rfl

/-- Compactness of reflection minus identity is exactly finiteness of off-line coordinates. -/
theorem compact_zeroReflection_sub_one_iff :
    IsCompactOperator (zeroReflection - 1 : ZeroSpace →L[ℂ] ZeroSpace) ↔
      {z : zetaZeroConfig.carrier | (z : ℂ).re ≠ 1 / 2}.Finite := by
  rw [zeroReflection_eq_permutationOperator, isCompact_permutationOperator_sub_one_iff]
  change {z : zetaZeroConfig.carrier | reflectCarrier zetaZeroConfig z ≠ z}.Finite ↔ _
  have he : {z : zetaZeroConfig.carrier | reflectCarrier zetaZeroConfig z ≠ z} =
      {z : zetaZeroConfig.carrier | (z : ℂ).re ≠ 1 / 2} := by
    ext z
    exact not_congr (zeroCarrier_reflection_fixed_iff z)
  rw [he]

#print axioms compact_zeroReflection_sub_one_iff
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
