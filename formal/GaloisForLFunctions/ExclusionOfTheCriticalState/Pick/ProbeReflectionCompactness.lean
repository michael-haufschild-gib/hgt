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

/-- The negative-sector projection is compact exactly when the off-line coordinates are finite. -/
theorem compact_negativePart_iff :
    IsCompactOperator (negativePart : ZeroSpace → ZeroSpace) ↔
      {z : zetaZeroConfig.carrier | (z : ℂ).re ≠ 1 / 2}.Finite := by
  have he : (negativePart : ZeroSpace → ZeroSpace) =
      (-1 / 2 : ℂ) • (fun x : ZeroSpace => (zeroReflection - 1) x) := by
    funext x
    change (1 / 2 : ℂ) • (x - zeroReflection x) =
      (-1 / 2 : ℂ) • (zeroReflection x - x)
    module
  rw [he, IsCompactOperator.smul_iff₀ (by norm_num : (-1 / 2 : ℂ) ≠ 0)]
  exact compact_zeroReflection_sub_one_iff

/-- A sector phase has compact defect precisely at trivial phase or finite off-line support. -/
theorem compact_phaseRotation_sub_one_iff (u : Circle) :
    IsCompactOperator ((phaseRotationEquiv u).toLinearIsometry.toContinuousLinearMap - 1 :
      ZeroSpace →L[ℂ] ZeroSpace) ↔ u = 1 ∨
      {z : zetaZeroConfig.carrier | (z : ℂ).re ≠ 1 / 2}.Finite := by
  have he : (fun x : ZeroSpace =>
      ((phaseRotationEquiv u).toLinearIsometry.toContinuousLinearMap - 1) x) =
      ((1 - (u : ℂ)) / 2) • (fun x : ZeroSpace => (zeroReflection - 1) x) := by
    funext x
    change phaseRotate u x - x = ((1 - (u : ℂ)) / 2) • (zeroReflection x - x)
    unfold phaseRotate positivePart negativePart
    module
  change IsCompactOperator (fun x : ZeroSpace =>
      ((phaseRotationEquiv u).toLinearIsometry.toContinuousLinearMap - 1) x) ↔ _
  rw [he]
  by_cases hu : u = 1
  · subst u
    simp only [Circle.coe_one, sub_self, zero_div, zero_smul, true_or, iff_true]
    exact IsCompactOperator.zero
  · have hc : (1 - (u : ℂ)) / 2 ≠ 0 := by
      apply div_ne_zero _ (by norm_num)
      intro h
      apply hu
      apply Subtype.ext
      exact (sub_eq_zero.mp h).symm
    rw [IsCompactOperator.smul_iff₀ hc]
    simpa only [hu, false_or] using compact_zeroReflection_sub_one_iff

#print axioms compact_zeroReflection_sub_one_iff
#print axioms compact_negativePart_iff
#print axioms compact_phaseRotation_sub_one_iff
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
