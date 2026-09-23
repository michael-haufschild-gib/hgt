import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpRelativePositionSymmetry
import GaloisForLFunctions.HTGeometry.FreeDifferentialClockShearCartan

/-!
# Euclidean displacement of the free differential clock shear

The rank-two clock shear has dominant Cartan vector `(n,-n)`.  This file evaluates the actual
Euclidean norm of that centered vector on the canonical projective completed-lattice orbit.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DifferentialFieldAut

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-- **Exact Euclidean displacement of the rank-two clock shear.**  The type-`A₁` root has length
`sqrt 2`, so the `n`-th canonical projective orbit vertex is at distance `sqrt 2 * n` from the
base vertex. -/
theorem freeClockShear_euclideanVertexDistance (n : ℕ) :
    DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
        (freeClockShearProjectiveBasePoint (C := C))
        ((freeClockShear (C := C) ^ n).projectiveBuildingAction
          (freeVariationalOreBasis (C := C) (r := 2))
          (freeClockShearProjectiveBasePoint (C := C))) =
      Real.sqrt 2 * n := by
  rw [projectiveBuildingAction_freeClockShear_pow_basePoint]
  unfold DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
  unfold freeClockShearProjectiveBasePoint
  rw [DiffOp.differentialVariationalProjectiveEuclideanRelativePosition_mk]
  change ‖WithLp.toLp 2 (DiffOp.centeredCoweight
    (DiffOp.completedPseudoDiffOpDominantRelativePosition
      (DiffOp.standardCompletedPseudoDiffOpLattice
        (K := JetField C (Fin 2)) (ι := Fin 2))
      (freeClockShearCompletedOrbitLattice (C := C) n)))‖ = _
  rw [completedPseudoDiffOpDominantRelativePosition_freeClockShear]
  rw [EuclideanSpace.norm_eq]
  simp [DiffOp.centeredCoweight, Fin.sum_univ_two]
  rw [show (n : ℝ) ^ (2 : ℕ) + (n : ℝ) ^ (2 : ℕ) = 2 * (n : ℝ) ^ (2 : ℕ) by ring,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2), Real.sqrt_sq_eq_abs]
  simp

end


end GaloisForLFunctions.HTGeometry.DifferentialFieldAut
