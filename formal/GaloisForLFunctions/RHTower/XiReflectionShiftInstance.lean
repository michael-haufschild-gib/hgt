import GaloisForLFunctions.RHTower.XiPairwiseShiftValueReflection
import GaloisForLFunctions.HTGeometry.ReflectionShiftGroupoid

/-!
# The completed Xi shift reflections are one instance of the abstract law

`XiPairwiseShiftValueReflection` proves the cocycle, swap, gauge and reflection laws for the
pairwise translate differences of `logDeriv xi`.  None of those proofs uses zeta: they use only
`logDeriv xi (1 - s) = - logDeriv xi s`, which is the functional equation transported to values.

Here the Xi objects are identified with the abstract ones, so the abstract laws apply verbatim, and
the abstract interface is discharged from `Differentiable ℂ xi` together with `xi (1 - s) = xi s`.
The same discharge works for any entire function with a reflection functional equation.

The abstract law also returns the vanishing of a value function at its reflection centre; for `xi`
that is the already-available `logDeriv_xi_one_half`, which the general statement
`HTGeometry.eq_zero_of_isReflectionAntisymmetric` now covers for every reflection-antisymmetric
value function at once.
-/

open Complex

namespace RHTower

noncomputable section

/-- **The Xi functional equation, as antisymmetry of a value function.** -/
theorem isReflectionAntisymmetric_logDeriv_xi :
    HTGeometry.IsReflectionAntisymmetric 1 (logDeriv xi) :=
  HTGeometry.isReflectionAntisymmetric_logDeriv xi_differentiable xi_one_sub

/-- The corpus's pairwise raw difference is the abstract oriented difference. -/
theorem xiPairwiseShiftRawLogDerivDifference_eq (a b s : ℂ) :
    xiPairwiseShiftRawLogDerivDifference a b s =
      HTGeometry.shiftDifference (logDeriv xi) a b s := by
  rw [xiPairwiseShiftRawLogDerivDifference, HTGeometry.shiftDifference]

/-- The corpus's pairwise reflection is the abstract pair reflection. -/
theorem xiPairwiseShiftReflection_eq (a b s : ℂ) :
    xiPairwiseShiftReflection a b s = HTGeometry.pairReflection 1 a b s := by
  rw [xiPairwiseShiftReflection, HTGeometry.pairReflection]

/-- The pairwise reflection law for Xi, obtained from the abstract law. -/
theorem xiPairwiseShiftRawLogDerivDifference_pairReflection (a b s : ℂ) :
    xiPairwiseShiftRawLogDerivDifference a b (xiPairwiseShiftReflection a b s) =
      xiPairwiseShiftRawLogDerivDifference a b s := by
  rw [xiPairwiseShiftReflection_eq, xiPairwiseShiftRawLogDerivDifference_eq,
    xiPairwiseShiftRawLogDerivDifference_eq]
  exact HTGeometry.shiftDifference_pairReflection isReflectionAntisymmetric_logDeriv_xi a b s

/-- **Antipodal Xi shift pairs give even differences.**  If the two shifts sum to one, the pairwise
difference is an even function of the observation point. -/
theorem xiPairwiseShiftRawLogDerivDifference_neg {a b : ℂ} (hab : a + b = 1) (s : ℂ) :
    xiPairwiseShiftRawLogDerivDifference a b (-s) =
      xiPairwiseShiftRawLogDerivDifference a b s := by
  rw [xiPairwiseShiftRawLogDerivDifference_eq, xiPairwiseShiftRawLogDerivDifference_eq]
  exact HTGeometry.shiftDifference_neg_of_add_eq isReflectionAntisymmetric_logDeriv_xi hab s

end

end RHTower
