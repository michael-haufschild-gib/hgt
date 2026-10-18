import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Orientation detected by an endpoint edge

Closing a symmetric tridiagonal path with one endpoint edge gives a cycle.
Reversing that edge changes its determinant by an exact nonzero monomial
when the edge and all path weights are nonzero. Two-row multilinearity
isolates the odd term; its cofactor is an upper-triangular path minor.
-/

noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty.CycleMatrix
set_option autoImplicit false

def path (k : ℕ) (d c : ℝ) : Matrix (Fin (k + 3)) (Fin (k + 3)) ℝ :=
  fun i j => if i.val = j.val then d
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then c else 0

def cycle (k : ℕ) (d c z : ℝ) : Matrix (Fin (k + 3)) (Fin (k + 3)) ℝ :=
  fun i j => if (i.val = 0 ∧ j.val = k + 2) ∨ (i.val = k + 2 ∧ j.val = 0)
    then z else path k d c i j

private theorem zero_ne_last (k : ℕ) : (0 : Fin (k + 3)) ≠ Fin.last (k + 2) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_zero, Fin.val_last] at hv
  omega

theorem path_symm (k : ℕ) (d c : ℝ) : (path k d c).IsSymm := by
  change (path k d c).transpose = path k d c
  ext i j
  simp only [Matrix.transpose_apply, path, eq_comm, or_comm]

/-- The closing edge is exactly a perturbation of the two endpoint rows. -/
theorem cycle_eq_updates (k : ℕ) (d c z : ℝ) :
    cycle k d c z =
      ((path k d c).updateRow 0
        ((path k d c) 0 + z • Pi.single (Fin.last (k + 2)) 1)).updateRow
          (Fin.last (k + 2)) ((path k d c) (Fin.last (k + 2)) + z • Pi.single 0 1) := by
  ext i j
  have hk0 : k + 2 ≠ 0 := by omega
  have hk1 : k + 2 ≠ 1 := by omega
  by_cases hi0 : i.val = 0 <;> by_cases hil : i.val = k + 2 <;>
    by_cases hj0 : j.val = 0 <;> by_cases hjl : j.val = k + 2 <;>
    simp_all [cycle, path, Matrix.updateRow_apply, Pi.single_apply, Fin.ext_iff]

private theorem two_rows_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (i j : ι) (hij : i ≠ j) (u v : ι → ℝ) (z : ℝ) :
    ((A.updateRow i (A i + z • u)).updateRow j (A j + z • v)).det =
      A.det + z * ((A.updateRow i u).det + (A.updateRow j v).det) +
        z ^ 2 * ((A.updateRow i u).updateRow j v).det := by
  have h0 : ((A.updateRow i (A i + z • u)).updateRow j (A j)).det =
      A.det + z * (A.updateRow i u).det := by
    rw [Matrix.updateRow_comm A hij, Matrix.updateRow_eq_self,
      Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  have h1 : ((A.updateRow i (A i + z • u)).updateRow j v).det =
      (A.updateRow j v).det + z * ((A.updateRow i u).updateRow j v).det := by
    rw [Matrix.updateRow_comm A hij, Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
      Matrix.updateRow_comm A hij.symm, Matrix.updateRow_eq_self,
      Matrix.updateRow_comm A hij.symm]
  rw [Matrix.det_updateRow_add, Matrix.det_updateRow_smul, h0, h1]
  ring

private def endpointMinor (k : ℕ) (d c : ℝ) : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ :=
  (path k d c).submatrix Fin.succ Fin.castSucc

private theorem endpointMinor_upper (k : ℕ) (d c : ℝ) :
    (endpointMinor k d c).BlockTriangular id := by
  intro i j hij
  change (j : ℕ) < (i : ℕ) at hij
  have h0 : i.val + 1 ≠ j.val := by omega
  have h1 : ¬ (i.val + 1 + 1 = j.val ∨ j.val + 1 = i.val + 1) := by omega
  simp [endpointMinor, path, Matrix.submatrix_apply, h0, h1]

private theorem endpointMinor_diag (k : ℕ) (d c : ℝ) (i : Fin (k + 2)) :
    endpointMinor k d c i i = c := by
  have h0 : i.val + 1 ≠ i.val := by omega
  simp [endpointMinor, path, Matrix.submatrix_apply, h0]

private theorem endpointMinor_det (k : ℕ) (d c : ℝ) :
    (endpointMinor k d c).det = c ^ (k + 2) := by
  rw [Matrix.det_of_upperTriangular (endpointMinor_upper k d c)]
  simp only [endpointMinor_diag, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The endpoint cofactor is independent of the path's diagonal entries. -/
theorem endpoint_cofactor (k : ℕ) (d c : ℝ) :
    ((path k d c).updateRow 0 (Pi.single (Fin.last (k + 2)) 1)).det =
      (-1 : ℝ) ^ (k + 2) * c ^ (k + 2) := by
  have hm : (((path k d c).updateRow 0 (Pi.single (Fin.last (k + 2)) 1)).submatrix
      Fin.succ (Fin.last (k + 2)).succAbove) = endpointMinor k d c := by
    ext i j
    simp [endpointMinor, Matrix.submatrix_apply]
  rw [Matrix.det_succ_row_zero, Finset.sum_eq_single (Fin.last (k + 2))]
  · simp only [Matrix.updateRow_self, Pi.single_eq_same, Fin.val_last, mul_one]
    rw [hm, endpointMinor_det]
  · intro j _ hj
    simp only [Matrix.updateRow_self, Pi.single_eq_of_ne hj, mul_zero, zero_mul]
  · simp

/-- Exact odd part of a cycle determinant under reversal of its closing edge. -/
theorem det_neg_sub_det (k : ℕ) (d c z : ℝ) :
    (cycle k d c (-z)).det - (cycle k d c z).det =
      -4 * z * (-1 : ℝ) ^ (k + 2) * c ^ (k + 2) := by
  have hx (x : ℝ) := two_rows_expansion (path k d c) 0 (Fin.last (k + 2))
    (zero_ne_last k) (Pi.single (Fin.last (k + 2)) 1) (Pi.single 0 1) x
  rw [← cycle_eq_updates] at hx
  have hc : ((path k d c).updateRow (Fin.last (k + 2)) (Pi.single 0 1)).det =
      ((path k d c).updateRow 0 (Pi.single (Fin.last (k + 2)) 1)).det := by
    rw [← Matrix.adjugate_apply, ← Matrix.adjugate_apply]
    exact ((path_symm k d c).adjugate.apply 0 (Fin.last (k + 2))).symm
  simp only [hx, hc, endpoint_cofactor]
  ring

end GaloisForLFunctions.BiScaleUncertainty.CycleMatrix
