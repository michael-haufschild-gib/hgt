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

/-! ## Off-diagonal physical matrix elements and the constraint ideal -/

/-- A physical bra annihilates every left-constraint matrix element.  Unlike the diagonal Ward
value below, the ket is arbitrary. -/
theorem constraintLeftWardMatrixElement_eq_zero
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (C L : E →L[𝕜] E) (hC : IsSelfAdjoint C) {φ ψ : E}
    (hφ : GaloisForLFunctions.PhysicalState C.toLinearMap φ) :
    inner 𝕜 φ (C (L ψ)) = 0 := by
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hC
  have h := hsym φ (L ψ)
  rw [GaloisForLFunctions.PhysicalState] at hφ
  rw [hφ] at h
  simpa using h.symm

/-- A physical ket annihilates every right-constraint matrix element.  Self-adjointness is not
needed on this side. -/
theorem constraintRightWardMatrixElement_eq_zero
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (C R : E →L[𝕜] E) {φ ψ : E}
    (hψ : GaloisForLFunctions.PhysicalState C.toLinearMap ψ) :
    inner 𝕜 φ (R (C ψ)) = 0 := by
  rw [GaloisForLFunctions.PhysicalState] at hψ
  change C ψ = 0 at hψ
  rw [hψ]
  simp

/-- Every operator in the two-sided ideal `C*L + R*C` has zero matrix elements between physical
states. -/
theorem constraintTwoSidedIdealMatrixElement_eq_zero
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (C L R : E →L[𝕜] E) (hC : IsSelfAdjoint C) {φ ψ : E}
    (hφ : GaloisForLFunctions.PhysicalState C.toLinearMap φ)
    (hψ : GaloisForLFunctions.PhysicalState C.toLinearMap ψ) :
    inner 𝕜 φ (((C * L + R * C) : E →L[𝕜] E) ψ) = 0 := by
  rw [add_apply, mul_apply_eq_comp, mul_apply_eq_comp, inner_add_right,
    constraintLeftWardMatrixElement_eq_zero C L hC hφ,
    constraintRightWardMatrixElement_eq_zero C R hψ, add_zero]

/-- **Dirac/RAQ representative independence.**  Operators differing by a two-sided constraint
ideal term have identical matrix elements between physical states. -/
theorem physicalMatrixElement_congr_mod_constraintTwoSidedIdeal
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (C A B L R : E →L[𝕜] E) (hC : IsSelfAdjoint C)
    (hmod : B = A + (C * L + R * C)) {φ ψ : E}
    (hφ : GaloisForLFunctions.PhysicalState C.toLinearMap φ)
    (hψ : GaloisForLFunctions.PhysicalState C.toLinearMap ψ) :
    inner 𝕜 φ (B ψ) = inner 𝕜 φ (A ψ) := by
  rw [hmod, add_apply, inner_add_right,
    constraintTwoSidedIdealMatrixElement_eq_zero C L R hC hφ hψ, add_zero]

/-! ## Quantitative constraint leakage -/

/-- On a physical state, the constraint leakage of an observable is exactly the commutator
applied to that state. -/
theorem constraintLeakage_eq_commutator_apply
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (C A : E →L[𝕜] E) {ψ : E}
    (hψ : GaloisForLFunctions.PhysicalState C.toLinearMap ψ) :
    C (A ψ) = ((C * A - A * C) : E →L[𝕜] E) ψ := by
  rw [sub_apply, mul_apply_eq_comp, mul_apply_eq_comp]
  rw [GaloisForLFunctions.PhysicalState] at hψ
  change C ψ = 0 at hψ
  rw [hψ]
  simp

/-- The commutator operator norm controls how far an observable moves a physical vector away from
the constraint kernel, measured by its constraint residual. -/
theorem norm_constraintLeakage_le_commutator
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (C A : E →L[𝕜] E) {ψ : E}
    (hψ : GaloisForLFunctions.PhysicalState C.toLinearMap ψ) :
    ‖C (A ψ)‖ ≤ ‖C * A - A * C‖ * ‖ψ‖ := by
  rw [constraintLeakage_eq_commutator_apply C A hψ]
  exact ContinuousLinearMap.le_opNorm _ _

/-- **Constraint Ward value.**  A physical state annihilates the value obtained by applying a
self-adjoint constraint after any bounded observable. -/
theorem constraintWardValue_eq_zero
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (C A : E →L[𝕜] E) (hC : IsSelfAdjoint C) {ψ : E}
    (hψ : GaloisForLFunctions.PhysicalState C.toLinearMap ψ) :
    inner 𝕜 ψ (C (A ψ)) = 0 := by
  exact constraintLeftWardMatrixElement_eq_zero C A hC hψ

/-- **Commutator Ward value.**  The expectation of `[C,A]` vanishes in every physical state of a
self-adjoint constraint. -/
theorem constraintCommutatorWardValue_eq_zero
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (C A : E →L[𝕜] E) (hC : IsSelfAdjoint C) {ψ : E}
    (hψ : GaloisForLFunctions.PhysicalState C.toLinearMap ψ) :
    inner 𝕜 ψ (((C * A - A * C) : E →L[𝕜] E) ψ) = 0 := by
  rw [sub_apply, mul_apply_eq_comp, mul_apply_eq_comp, inner_sub_right,
    constraintWardValue_eq_zero C A hC hψ]
  rw [GaloisForLFunctions.PhysicalState] at hψ
  change C ψ = 0 at hψ
  rw [hψ]
  simp

end HTGeometry
