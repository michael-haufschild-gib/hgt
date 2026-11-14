import GaloisForLFunctions.HTGeometry.LinearAlgebra.BlockTriangularRank
import GaloisForLFunctions.HTGeometry.HorizonJacobianDeterminant
import Mathlib.Tactic

/-!
# Rank and nullity of the horizon observation Jacobian

The observation Jacobian has a reciprocal-Jacobian block and an identity block.
The identity block absorbs every off-diagonal contribution, so it adds exactly
`n` to the rank and leaves the nullity unchanged. These formulas hold at singular
points as well as at regular points.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
variable {K : Type*} [Field K]

/-- The identity block contributes exactly its size to the observation rank. -/
theorem rank_horizonObservationJacobian (Y : Polynomial K) (n m : ℕ) :
    (horizonObservationJacobian Y n m).rank =
      (criticalReciprocalJacobian Y n m).rank + n := by
  rw [horizonObservationJacobian_eq_fromBlocks, rank_fromBlocks_zero_upper_one,
    Matrix.rank_transpose, Fintype.card_fin]

/-- All null directions come from the reciprocal Jacobian, including at singular points. -/
theorem nullity_horizonObservationJacobian (Y : Polynomial K) (n m : ℕ) :
    Module.finrank K (LinearMap.ker (horizonObservationJacobian Y n m).mulVecLin) =
      Module.finrank K (LinearMap.ker (criticalReciprocalJacobian Y n m).mulVecLin) := by
  have hfull := (horizonObservationJacobian Y n m).mulVecLin.finrank_range_add_finrank_ker
  have hrecip := (criticalReciprocalJacobian Y n m).mulVecLin.finrank_range_add_finrank_ker
  change (horizonObservationJacobian Y n m).rank + _ = _ at hfull
  change (criticalReciprocalJacobian Y n m).rank + _ = _ at hrecip
  rw [rank_horizonObservationJacobian, Module.finrank_pi, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_fin] at hfull
  rw [Module.finrank_pi, Fintype.card_fin] at hrecip
  omega

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.rank_horizonObservationJacobian
#print axioms GaloisForLFunctions.HTGeometry.nullity_horizonObservationJacobian
