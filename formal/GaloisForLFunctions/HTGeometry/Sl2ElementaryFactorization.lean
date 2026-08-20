import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Elementary factorization of two-by-two matrices of determinant one

A matrix of determinant one with nonzero lower-left entry is the explicit product
`u⁺((a-1)/c) · u⁻(c) · u⁺((d-1)/c)`, and one lower elementary factor moves any determinant-one
matrix into that case, so every such matrix is a product of four elementary matrices.

This is what lets a cocycle be evaluated on the whole group once it is known on the two elementary
one-parameter subgroups.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C : Type*} [Field C]

/-- The upper elementary matrix. -/
def sl2UPlus (x : C) : Matrix (Fin 2) (Fin 2) C := !![1, x; 0, 1]

/-- The lower elementary matrix. -/
def sl2UMinus (y : C) : Matrix (Fin 2) (Fin 2) C := !![1, 0; y, 1]

@[simp] theorem det_uPlus (x : C) : (sl2UPlus x).det = 1 := by
  rw [sl2UPlus, Matrix.det_fin_two_of]; ring

@[simp] theorem det_uMinus (y : C) : (sl2UMinus y).det = 1 := by
  rw [sl2UMinus, Matrix.det_fin_two_of]; ring

@[simp] theorem uPlus_zero : sl2UPlus (0 : C) = 1 := by
  rw [sl2UPlus]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp] theorem uMinus_zero : sl2UMinus (0 : C) = 1 := by
  rw [sl2UMinus]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem uPlus_mul_uPlus (x y : C) : sl2UPlus x * sl2UPlus y = sl2UPlus (x + y) := by
  rw [sl2UPlus, sl2UPlus, sl2UPlus, Matrix.mul_fin_two]
  norm_num [add_comm]

theorem uMinus_mul_uMinus (x y : C) : sl2UMinus x * sl2UMinus y = sl2UMinus (x + y) := by
  rw [sl2UMinus, sl2UMinus, sl2UMinus, Matrix.mul_fin_two]
  norm_num [add_comm]

/-- **The Bruhat factorization** of a determinant-one matrix with nonzero lower-left entry. -/
theorem eq_uPlus_mul_uMinus_mul_uPlus (M : Matrix (Fin 2) (Fin 2) C) (hdet : M.det = 1)
    (hc : M 1 0 ≠ 0) :
    M = sl2UPlus ((M 0 0 - 1) / M 1 0) * sl2UMinus (M 1 0) * sl2UPlus ((M 1 1 - 1) / M 1 0) := by
  rw [Matrix.det_fin_two] at hdet
  have hmul : sl2UPlus ((M 0 0 - 1) / M 1 0) * sl2UMinus (M 1 0) * sl2UPlus ((M 1 1 - 1) / M 1 0)
      = !![M 0 0, (M 0 0 * M 1 1 - 1) / M 1 0; M 1 0, M 1 1] := by
    rw [sl2UPlus, sl2UMinus, sl2UPlus, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring
  rw [hmul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  field_simp
  linear_combination -hdet

/-- **Every determinant-one matrix is a product of elementary matrices.** -/
theorem exists_elementary_factorization (M : Matrix (Fin 2) (Fin 2) C) (hdet : M.det = 1) :
    ∃ x y z w : C, M = sl2UPlus x * sl2UMinus y * sl2UPlus z * sl2UMinus w := by
  by_cases hc : M 1 0 = 0
  · have hd : M 1 1 ≠ 0 := by
      intro hzero
      rw [Matrix.det_fin_two, hc, hzero] at hdet
      simp at hdet
    have hMu : (M * sl2UMinus (1 : C)) 1 0 = M 1 1 := by
      rw [Matrix.mul_apply, Fin.sum_univ_two, sl2UMinus]
      simp [hc]
    have hdet' : (M * sl2UMinus (1 : C)).det = 1 := by
      rw [Matrix.det_mul, hdet, det_uMinus, mul_one]
    have hfac := eq_uPlus_mul_uMinus_mul_uPlus (M * sl2UMinus (1 : C)) hdet' (by rw [hMu]; exact hd)
    refine ⟨((M * sl2UMinus (1 : C)) 0 0 - 1) / (M * sl2UMinus (1 : C)) 1 0,
      (M * sl2UMinus (1 : C)) 1 0,
      ((M * sl2UMinus (1 : C)) 1 1 - 1) / (M * sl2UMinus (1 : C)) 1 0, -1, ?_⟩
    rw [← hfac]
    rw [mul_assoc, uMinus_mul_uMinus]
    norm_num
  · refine ⟨(M 0 0 - 1) / M 1 0, M 1 0, (M 1 1 - 1) / M 1 0, 0, ?_⟩
    rw [uMinus_zero, mul_one]
    exact eq_uPlus_mul_uMinus_mul_uPlus M hdet hc

end

end GaloisForLFunctions.HTGeometry
