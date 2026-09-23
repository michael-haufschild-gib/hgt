import GaloisForLFunctions.HTGeometry.QuantumNullSpaceTransport

/-!
# Least-squares Gram and force identities for quantum dynamics

The normal-equation structure `G = O†O`, `F = O†E` used in arXiv:2609.07645 is
captured without rank or invertibility assumptions. The exact residual update exposes
the linear interference term and nonnegative quadratic Gram term.
-/

set_option autoImplicit false
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry
noncomputable section

def leastSquaresResidual
    {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (O : X →ₗ[ℂ] Y) (E : Y) (v : X) : Y := O v - E

/-- Exact least-squares loss along every parameter increment. -/
theorem leastSquaresResidual_update
    {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (O : X →ₗ[ℂ] Y) (E : Y) (v w : X) :
    ‖leastSquaresResidual O E (v + w)‖ ^ (2 : ℕ) =
      ‖leastSquaresResidual O E v‖ ^ (2 : ℕ) +
        2 * (inner ℂ (leastSquaresResidual O E v) (O w)).re + ‖O w‖ ^ (2 : ℕ) := by
  have h := norm_add_sq (𝕜 := ℂ) (leastSquaresResidual O E v) (O w)
  have hr : leastSquaresResidual O E (v + w) = leastSquaresResidual O E v + O w := by
    unfold leastSquaresResidual
    rw [map_add]
    abel
  rw [hr]
  exact h

/-- Sesquilinear Gram form induced by the observation/Jacobian map. -/
def leastSquaresGram
    {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (O : X →ₗ[ℂ] Y) (w v : X) : ℂ := inner ℂ (O w) (O v)

/-- Force covector induced by the target energy derivative. -/
def leastSquaresForce
    {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (O : X →ₗ[ℂ] Y) (E : Y) (w : X) : ℂ := inner ℂ (O w) E

/-- Normal-equation defect equals residual tested against every observation direction. -/
theorem leastSquares_normalEquation_residual
    {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (O : X →ₗ[ℂ] Y) (E : Y) (v w : X) :
    inner ℂ (O w) (leastSquaresResidual O E v) =
      leastSquaresGram O w v - leastSquaresForce O E w := by
  simp [leastSquaresResidual, leastSquaresGram, leastSquaresForce]

end
end GaloisForLFunctions.HTGeometry
