import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Exact determinant recurrence under row replacement

Replacing a row by `delta` expands as a sum of determinants obtained by replacing each column by
the corresponding coordinate vector. This is the exact algebraic recurrence used to lift the
k-server work-function update before applying a valuation.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Row-linearity written as a sum over coordinate rows. -/
theorem det_updateRow_eq_sum_replacementDet
    (A : Matrix n n R) (i : n) (delta : n → R) :
    (A.updateRow i delta).det =
      ∑ j : n, delta j * (A.updateRow i (Pi.single j 1)).det := by
  rw [Matrix.det_eq_sum_mul_adjugate_row]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.updateRow_self, Matrix.adjugate_apply, Matrix.updateRow_idem]

/-- A coordinate-row replacement and the dual coordinate-column replacement have equal
determinants: both compute the same cofactor. -/
theorem det_updateRow_single_eq_det_updateCol_single
    (A : Matrix n n R) (i j : n) :
    (A.updateRow i (Pi.single j 1)).det =
      (A.updateCol j (Pi.single i 1)).det := by
  rw [← Matrix.adjugate_apply]
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  simp [Matrix.mulVec]

/-- **Exact lifted row-replacement recurrence.** Each coefficient of the new row multiplies the
old determinant with that column replaced by the normalized request vector. -/
theorem det_updateRow_eq_sum_columnReplacementDet
    (A : Matrix n n R) (i : n) (delta : n → R) :
    (A.updateRow i delta).det =
      ∑ j : n, delta j * (A.updateCol j (Pi.single i 1)).det := by
  rw [det_updateRow_eq_sum_replacementDet]
  apply Finset.sum_congr rfl
  intro j _
  rw [det_updateRow_single_eq_det_updateCol_single]

end GaloisForLFunctions.HTGeometry
