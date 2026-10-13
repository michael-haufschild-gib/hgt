import GaloisForLFunctions.HTGeometry.FiniteModalHankelRank

/-! # Exact determinant of centered finite power moments -/

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry
open scoped BigOperators

/-- Removing the constant coordinate from a normalized moment matrix leaves the
centered moment determinant unchanged. -/
theorem det_algebraicHankelMatrix_eq_centered {K : Type*} [CommRing K]
    (s : ℕ → K) (n : ℕ) (h0 : s 0 = 1) :
    (algebraicHankelMatrix s (n + 1)).det =
      (Matrix.of fun i j : Fin n => s ((i.val + 1) + (j.val + 1)) -
        s (i.val + 1) * s (j.val + 1)).det := by
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) K := fun i j =>
    s (i.val + j.val) + (if i = 0 then 0 else -s i.val) * s j.val
  have hdet : B.det = (algebraicHankelMatrix s (n + 1)).det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const
      (fun i => if i = 0 then 0 else -s i.val) 0 (by simp)
    intro i j
    simp only [B, algebraicHankelMatrix, Fin.val_zero, zero_add]
  rw [← hdet, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [B, h0, Matrix.submatrix, sub_eq_add_neg]

/-- At maximal degree, the centered power determinant is the squared
Vandermonde determinant times the product of normalized weights. -/
theorem det_finite_power_covariance {K : Type*} [CommRing K] {n : ℕ}
    (w x : Fin (n + 1) → K) (hw : ∑ i, w i = 1) :
    (Matrix.of fun i j : Fin n =>
      (∑ l, w l * x l ^ ((i.val + 1) + (j.val + 1))) -
        (∑ l, w l * x l ^ (i.val + 1)) *
          (∑ l, w l * x l ^ (j.val + 1))).det =
      (Matrix.vandermonde x).det ^ 2 * ∏ l, w l := by
  exact (det_algebraicHankelMatrix_eq_centered (finiteModalSequence w x) n
    (by simpa [finiteModalSequence] using hw)).symm.trans
    (det_algebraicHankelMatrix_finiteModalSequence w x)

end GaloisForLFunctions.HTGeometry
