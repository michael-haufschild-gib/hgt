import GaloisForLFunctions.HTGeometry.DifferentialOperatorCartanExtrema
import GaloisForLFunctions.HTGeometry.FreeDifferentialVariationalOreBasis

/-!
# Free differential order as the top completed Cartan coordinate

In every positive free differential rank, the order of a differential automorphism is exactly the
top coordinate of the canonical dominant relative-position vector from the completed variational
orbit lattice back to the standard lattice.  The order convention is explicit and matches the
matrix-degree orientation of the Fréchet Jacobian.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DifferentialFieldAut

noncomputable section

variable {C : Type u} [Field C] [CharZero C] {r : ℕ}

/-- Equation `(19)`: free differential order is the top canonical completed Cartan coordinate. -/
theorem freeDifferentialOrder_eq_topCartan
    (σ : FreeAut (C := C) (ι := Fin (r + 1))) :
    DiffOp.completedPseudoDiffOpDominantRelativePosition
        (DiffOp.mapCompletedPseudoDiffOpLatticeLinear
          (DiffOp.completedPseudoDiffOpMatrixLinearEquiv
            (DiffOp.completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit
              (variationalOreOperatorMatrixUnit σ.fixes σ.deriv_comm
                (freeVariationalOreBasis (C := C) (r := r + 1)))))
          (DiffOp.standardCompletedPseudoDiffOpLattice
            (K := JetField C (Fin (r + 1))) (ι := Fin (r + 1))))
        (DiffOp.standardCompletedPseudoDiffOpLattice
          (K := JetField C (Fin (r + 1))) (ι := Fin (r + 1))) 0 =
      (freeDifferentialOrder σ : ℤ) := by
  rw [DiffOp.completedPseudoDiffOpDominantRelativePosition_mapMatrix_standard_zero_eq_matDeg]
  rw [variationalOreOperatorMatrixUnit_free_val]
  rfl

/-- Equation `(19)` for every finite iterate of a free differential automorphism. -/
theorem freeDifferentialOrder_pow_eq_topCartan
    (σ : FreeAut (C := C) (ι := Fin (r + 1))) (n : ℕ) :
    DiffOp.completedPseudoDiffOpDominantRelativePosition
        (DiffOp.mapCompletedPseudoDiffOpLatticeLinear
          (DiffOp.completedPseudoDiffOpMatrixLinearEquiv
            (DiffOp.completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit
              (variationalOreOperatorMatrixUnit (σ ^ n).fixes (σ ^ n).deriv_comm
                (freeVariationalOreBasis (C := C) (r := r + 1)))))
          (DiffOp.standardCompletedPseudoDiffOpLattice
            (K := JetField C (Fin (r + 1))) (ι := Fin (r + 1))))
        (DiffOp.standardCompletedPseudoDiffOpLattice
          (K := JetField C (Fin (r + 1))) (ι := Fin (r + 1))) 0 =
      (freeDifferentialOrder (σ ^ n) : ℤ) := by
  exact freeDifferentialOrder_eq_topCartan (σ ^ n)

end


end DifferentialFieldAut

end GaloisForLFunctions.HTGeometry
