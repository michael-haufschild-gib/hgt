import GaloisForLFunctions.HTGeometry.AuxiliaryTorsionElimination
import GaloisForLFunctions.HTGeometry.SchurComplementKernel

/-!
# Auxiliary torsion as a scalar Schur complement

The algebraic torsion field is a one-dimensional block with boundary operator `-1`.  Eliminating
that block through the corpus's Schur-complement construction produces exactly the contact
quadratic form obtained by completing the square.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Scalar source-to-torsion coupling with positive strength encoded logarithmically. -/
def auxiliaryTorsionCoupling (logKappa : ℝ) : Module.End ℝ ℝ :=
  Real.exp (logKappa / 2) • LinearMap.id

/-- Negative unit quadratic block of the normalized auxiliary field. -/
def auxiliaryTorsionBoundary : Module.End ℝ ℝ := -LinearMap.id

/-- Schur complement left after eliminating the normalized auxiliary field. -/
def auxiliaryTorsionSchurComplement (logKappa : ℝ) : Module.End ℝ ℝ :=
  schurComplement 0 (auxiliaryTorsionCoupling logKappa)
    (auxiliaryTorsionCoupling logKappa) auxiliaryTorsionBoundary

/-- The negative unit boundary block is its own inverse. -/
theorem auxiliaryTorsionBoundary_selfInverse (source : ℝ) :
    auxiliaryTorsionBoundary (auxiliaryTorsionBoundary source) = source := by
  simp [auxiliaryTorsionBoundary]

/-- Scalar Schur elimination produces multiplication by the positive contact coefficient. -/
theorem auxiliaryTorsionSchurComplement_apply (logKappa source : ℝ) :
    auxiliaryTorsionSchurComplement logKappa source = Real.exp logKappa * source := by
  rw [auxiliaryTorsionSchurComplement, schurComplement_apply]
  simp [auxiliaryTorsionCoupling, auxiliaryTorsionBoundary]
  rw [← mul_assoc, ← Real.exp_add,
    show logKappa / 2 + logKappa / 2 = logKappa by ring]

/-- Schur-complement quadratic energy equals the completed-square contact Lagrangian. -/
theorem auxiliaryTorsionSchurQuadratic_eq_contact (logKappa source : ℝ) :
    auxiliaryTorsionSchurComplement logKappa source * source / 2 =
      eliminatedContactLagrangian logKappa source := by
  rw [auxiliaryTorsionSchurComplement_apply, eliminatedContactLagrangian_eq]
  ring

/-- Existing block-kernel elimination recovers the forced auxiliary response with no side
conditions. -/
theorem auxiliaryTorsionBlock_eq_zero_iff (logKappa : ℝ) (p : ℝ × ℝ) :
    schurBlockOperator 0 (auxiliaryTorsionCoupling logKappa)
        (auxiliaryTorsionCoupling logKappa) auxiliaryTorsionBoundary p = 0 ↔
      auxiliaryTorsionSchurComplement logKappa p.1 = 0 ∧
        p.2 = Real.exp (logKappa / 2) * p.1 := by
  rw [schurBlockOperator_apply_eq_zero_iff auxiliaryTorsionBoundary_selfInverse
    auxiliaryTorsionBoundary_selfInverse]
  simp [auxiliaryTorsionSchurComplement, auxiliaryTorsionCoupling,
    auxiliaryTorsionBoundary]

end GaloisForLFunctions.HTGeometry
