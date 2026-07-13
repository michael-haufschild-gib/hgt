import GaloisForLFunctions.HTGeometry.FrozenConstraint
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Ward value relations for static quantum constraints

For a bounded self-adjoint constraint `C`, a physical state satisfies `C psi = 0`.  Symmetry then
turns the operator constraint into scalar value relations: `inner psi (C (A psi)) = 0` for every
bounded observable `A`, and hence the expectation of the commutator `[C,A]` vanishes.

This is the finite Hilbert-space algebra behind the Ward/Dirac-observable face of a
Wheeler--DeWitt constraint.  It is static: no Schrödinger evolution or clock is introduced.
-/

namespace HTGeometry

/-- **Constraint Ward value.**  A physical state annihilates the value obtained by applying a
self-adjoint constraint after any bounded observable. -/
theorem constraintWardValue_eq_zero
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (C A : E →L[𝕜] E) (hC : IsSelfAdjoint C) {ψ : E}
    (hψ : GaloisForLFunctions.PhysicalState C.toLinearMap ψ) :
    inner 𝕜 ψ (C (A ψ)) = 0 := by
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hC
  have h := hsym ψ (A ψ)
  rw [GaloisForLFunctions.PhysicalState] at hψ
  rw [hψ] at h
  simpa using h.symm

/-- **Commutator Ward value.**  The expectation of `[C,A]` vanishes in every physical state of a
self-adjoint constraint. -/
theorem constraintCommutatorWardValue_eq_zero
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (C A : E →L[𝕜] E) (hC : IsSelfAdjoint C) {ψ : E}
    (hψ : GaloisForLFunctions.PhysicalState C.toLinearMap ψ) :
    inner 𝕜 ψ (((C * A - A * C) : E →L[𝕜] E) ψ) = 0 := by
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.mul_apply, inner_sub_right,
    constraintWardValue_eq_zero C A hC hψ]
  rw [GaloisForLFunctions.PhysicalState] at hψ
  change C ψ = 0 at hψ
  rw [hψ]
  simp

end HTGeometry
