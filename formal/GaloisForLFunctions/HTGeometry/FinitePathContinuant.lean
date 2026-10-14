import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Exact determinant recurrence for finite path matrices

Vertices are ordered newest first, so deleting the first row and column
recovers the preceding path. Two literal Laplace expansions give the
continuant recurrence over an arbitrary commutative ring.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

variable {R : Type*} [CommRing R]

def finitePathMatrix (d u l : ℕ → R) : (N : ℕ) → Matrix (Fin N) (Fin N) R
  | 0 => fun i => Fin.elim0 i
  | N + 1 => fun i j =>
      Fin.cases (Fin.cases (d N) (fun j => if (j : ℕ) = 0 then u (N - 1) else 0) j)
        (fun i => Fin.cases (if (i : ℕ) = 0 then l (N - 1) else 0)
          (fun j => finitePathMatrix d u l N i j) j) i

@[simp] theorem finitePathMatrix_zero_zero (d u l : ℕ → R) (N : ℕ) :
    finitePathMatrix d u l (N + 1) 0 0 = d N := rfl

@[simp] theorem finitePathMatrix_zero_succ (d u l : ℕ → R) (N : ℕ) (j : Fin N) :
    finitePathMatrix d u l (N + 1) 0 j.succ =
      if (j : ℕ) = 0 then u (N - 1) else 0 := rfl

@[simp] theorem finitePathMatrix_succ_zero (d u l : ℕ → R) (N : ℕ) (i : Fin N) :
    finitePathMatrix d u l (N + 1) i.succ 0 =
      if (i : ℕ) = 0 then l (N - 1) else 0 := rfl

@[simp] theorem finitePathMatrix_succ_succ (d u l : ℕ → R) (N : ℕ) (i j : Fin N) :
    finitePathMatrix d u l (N + 1) i.succ j.succ = finitePathMatrix d u l N i j := rfl

theorem finitePathMatrix_tail (d u l : ℕ → R) (N : ℕ) :
    (finitePathMatrix d u l (N + 1)).submatrix Fin.succ Fin.succ = finitePathMatrix d u l N := rfl

@[simp] theorem finitePathMatrix_zero_one (d u l : ℕ → R) (N : ℕ) :
    finitePathMatrix d u l (N + 2) 0 1 = u N := by
  rw [← Fin.succ_zero_eq_one, finitePathMatrix_zero_succ]
  simp

@[simp] theorem finitePathMatrix_one_zero (d u l : ℕ → R) (N : ℕ) :
    finitePathMatrix d u l (N + 2) 1 0 = l N := by
  rw [← Fin.succ_zero_eq_one, finitePathMatrix_succ_zero]
  simp

private theorem first_offDiagonal_minor_det (d u l : ℕ → R) (N : ℕ) :
    ((finitePathMatrix d u l (N + 2)).submatrix Fin.succ
      (1 : Fin (N + 2)).succAbove).det = l N * (finitePathMatrix d u l N).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hminor :
      (((finitePathMatrix d u l (N + 2)).submatrix Fin.succ
        (1 : Fin (N + 2)).succAbove).submatrix
          (0 : Fin (N + 1)).succAbove Fin.succ) = finitePathMatrix d u l N := by
    ext i j
    simp only [Matrix.submatrix_apply, Fin.zero_succAbove, Fin.one_succAbove_succ,
      finitePathMatrix_succ_succ]
  rw [hminor]
  simp [Matrix.submatrix_apply]

theorem det_finitePathMatrix_succ_succ (d u l : ℕ → R) (N : ℕ) :
    (finitePathMatrix d u l (N + 2)).det =
      d (N + 1) * (finitePathMatrix d u l (N + 1)).det -
        u N * l N * (finitePathMatrix d u l N).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have htail : (finitePathMatrix d u l (N + 2)).submatrix Fin.succ
      (0 : Fin (N + 2)).succAbove = finitePathMatrix d u l (N + 1) := by
    rw [Fin.succAbove_zero]
    rfl
  rw [htail, Fin.sum_univ_succ]
  simp [first_offDiagonal_minor_det, sub_eq_add_neg, mul_assoc]

end
end GaloisForLFunctions.HTGeometry
