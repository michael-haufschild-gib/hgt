import GaloisForLFunctions.HTGeometry.QuantumLeastSquaresGram

/-!
# Stationarity and null directions for quantum least squares

Closed consequences of the normal equations in arXiv:2609.07645. Stationarity is
encoded as data, yielding an exact Pythagorean loss law and a global minimum. Kernel
increments remain exactly flat even without stationarity.
-/

set_option autoImplicit false
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry
noncomputable section

def leastSquaresLoss
    {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (O : X →ₗ[ℂ] Y) (E : Y) (v : X) : ℝ := ‖leastSquaresResidual O E v‖ ^ (2 : ℕ)

/-- A normal-equation solution, packaged without theorem premises. -/
structure LeastSquaresStationaryPoint
    {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (O : X →ₗ[ℂ] Y) (E : Y) where
  parameter : X
  residual_orthogonal : ∀ w : X,
    inner ℂ (leastSquaresResidual O E parameter) (O w) = 0

/-- Stationarity removes the interference term from every loss update. -/
theorem leastSquaresLoss_stationary_update
    {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (O : X →ₗ[ℂ] Y) (E : Y) (v : LeastSquaresStationaryPoint O E) (w : X) :
    leastSquaresLoss O E (v.parameter + w) =
      leastSquaresLoss O E v.parameter + ‖O w‖ ^ (2 : ℕ) := by
  rw [leastSquaresLoss, leastSquaresLoss, leastSquaresResidual_update,
    v.residual_orthogonal]
  simp

/-- Every stationary point is a global least-squares minimizer. -/
theorem leastSquaresLoss_stationary_minimizes
    {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (O : X →ₗ[ℂ] Y) (E : Y) (v : LeastSquaresStationaryPoint O E) (w : X) :
    leastSquaresLoss O E v.parameter ≤ leastSquaresLoss O E (v.parameter + w) := by
  rw [leastSquaresLoss_stationary_update]
  exact le_add_of_nonneg_right (sq_nonneg ‖O w‖)

/-- Every QGT/Jacobian kernel increment is an exactly flat loss direction. -/
theorem leastSquaresLoss_add_kernel
    {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (O : X →ₗ[ℂ] Y) (E : Y) (v : X) (w : LinearMap.ker O) :
    leastSquaresLoss O E (v + w.1) = leastSquaresLoss O E v := by
  rw [leastSquaresLoss, leastSquaresLoss, leastSquaresResidual_update]
  have hw : O w.1 = 0 := w.property
  rw [hw]
  simp

end
end GaloisForLFunctions.HTGeometry
