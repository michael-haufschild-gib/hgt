import Mathlib

/-!
# The Cauchy determinant

The matrix with entries `(x i + y j)⁻¹` has determinant

`∏_{i<j} (x i - x j)(y i - y j) / ∏_{i,j} (x i + y j)`.

The proof is the classical two-step elimination.  Subtracting the first row from every other row
produces the factor `x 0 - x i` in row `i` and `(x 0 + y j)⁻¹` in column `j`; subtracting the first
column from every other column then produces `y 0 - y j` in column `j` and `(x i + y 0)⁻¹` in row
`i`, and a cofactor expansion along the resulting first row leaves the Cauchy matrix of one lower
size.
-/

open Finset Matrix

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

/-- The Cauchy matrix of two families. -/
def cauchyMatrix {n : ℕ} (x y : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => (x i + y j)⁻¹

@[simp] theorem cauchyMatrix_apply {n : ℕ} (x y : Fin n → K) (i j : Fin n) :
    cauchyMatrix x y i j = (x i + y j)⁻¹ := rfl

/-- **The Cauchy determinant.** -/
theorem det_cauchyMatrix : ∀ {n : ℕ} (x y : Fin n → K), (∀ i j, x i + y j ≠ 0) →
    (cauchyMatrix x y).det * ∏ i, ∏ j, (x i + y j) =
      ∏ i, ∏ j ∈ Finset.Ioi i, ((x i - x j) * (y i - y j)) := by
  intro n
  induction n with
  | zero => intro x y _; simp
  | succ n ih =>
    intro x y hxy
    classical
    -- Subtract the first row from every other row.
    set B : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.of fun i j =>
      if i = 0 then (x 0 + y j)⁻¹
      else (x 0 - x i) * ((x i + y j)⁻¹ * (x 0 + y j)⁻¹) with hB
    have hBdet : B.det = (cauchyMatrix x y).det := by
      refine Matrix.det_eq_of_forall_row_eq_smul_add_const
        (fun i => if i = 0 then (0 : K) else -1) 0 (by simp) ?_
      intro i j
      by_cases hi : i = 0
      · subst hi; simp [hB]
      · have h1 : x i + y j ≠ 0 := hxy i j
        have h0 : x 0 + y j ≠ 0 := hxy 0 j
        simp only [hB, Matrix.of_apply, hi, if_false, cauchyMatrix_apply]
        field_simp
        ring
    -- Factor the row and column scalars out.
    set f : Fin (n + 1) → K := fun i => if i = 0 then 1 else x 0 - x i with hf
    set g : Fin (n + 1) → K := fun j => (x 0 + y j)⁻¹ with hg
    set C : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.of fun i j =>
      if i = 0 then 1 else (x i + y j)⁻¹ with hC
    have hBfac : B = Matrix.of fun i j => f i * (Matrix.of fun i j => g j * C i j) i j := by
      ext i j
      by_cases hi : i = 0
      · subst hi; simp [hB, hf, hg, hC]
      · simp only [hB, hf, hg, hC, Matrix.of_apply, hi, if_false]
        ring
    have hBdet' : B.det = (∏ i, f i) * ((∏ j, g j) * C.det) := by
      rw [hBfac, Matrix.det_mul_column, Matrix.det_mul_row]
    -- Subtract the first column from every other column.
    set D : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.of fun i j =>
      if j = 0 then (if i = 0 then (1 : K) else (x i + y 0)⁻¹)
      else if i = 0 then 0 else (y 0 - y j) * ((x i + y j)⁻¹ * (x i + y 0)⁻¹) with hD
    have hDdet : D.det = C.det := by
      rw [← Matrix.det_transpose D, ← Matrix.det_transpose C]
      refine Matrix.det_eq_of_forall_row_eq_smul_add_const
        (fun j => if j = 0 then (0 : K) else -1) 0 (by simp) ?_
      intro j i
      by_cases hj : j = 0
      · subst hj; simp [hD, hC]
      · by_cases hi : i = 0
        · subst hi; simp [hD, hC, hj]
        · have h1 : x i + y j ≠ 0 := hxy i j
          have h0 : x i + y 0 ≠ 0 := hxy i 0
          simp only [hD, hC, Matrix.transpose_apply, Matrix.of_apply, hj, hi, if_false]
          field_simp
          ring
    -- Expand along the first row.
    have hDsub : D.det = (D.submatrix Fin.succ Fin.succ).det := by
      rw [Matrix.det_succ_row_zero]
      rw [Finset.sum_eq_single 0]
      · simp [hD, Fin.succAbove_zero]
      · intro j _ hj
        simp [hD, hj]
      · intro h
        exact absurd (Finset.mem_univ (0 : Fin (n + 1))) h
    -- Identify the submatrix with a scaled Cauchy matrix of size `n`.
    set h' : Fin n → K := fun i => (x i.succ + y 0)⁻¹ with hh'
    set k' : Fin n → K := fun j => y 0 - y j.succ with hk'
    have hsub : D.submatrix Fin.succ Fin.succ =
        Matrix.of fun i j => h' i *
          (Matrix.of fun i j => k' j *
            cauchyMatrix (fun i : Fin n => x i.succ) (fun j : Fin n => y j.succ) i j) i j := by
      ext i j
      simp only [hD, hh', hk', Matrix.submatrix_apply, Matrix.of_apply, cauchyMatrix_apply,
        Fin.succ_ne_zero, if_false]
      ring
    have hsubdet : (D.submatrix Fin.succ Fin.succ).det =
        (∏ i, h' i) * ((∏ j, k' j) *
          (cauchyMatrix (fun i : Fin n => x i.succ) (fun j : Fin n => y j.succ)).det) := by
      rw [hsub, Matrix.det_mul_column, Matrix.det_mul_row]
    -- Assemble.
    have hihyp : ∀ i j : Fin n, x i.succ + y j.succ ≠ 0 := fun i j => hxy _ _
    have hrec := ih (fun i : Fin n => x i.succ) (fun j : Fin n => y j.succ) hihyp
    have hdet : (cauchyMatrix x y).det =
        (∏ i, f i) * ((∏ j, g j) * ((∏ i, h' i) * ((∏ j, k' j) *
          (cauchyMatrix (fun i : Fin n => x i.succ) (fun j : Fin n => y j.succ)).det))) := by
      rw [← hBdet, hBdet', ← hDdet, hDsub, hsubdet]
    have hfprod : (∏ i, f i) = ∏ j ∈ Finset.Ioi (0 : Fin (n + 1)), (x 0 - x j) := by
      rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero]
      simp [hf, Fin.succ_ne_zero]
    have hkprod : (∏ j, k' j) = ∏ j ∈ Finset.Ioi (0 : Fin (n + 1)), (y 0 - y j) := by
      rw [Fin.prod_Ioi_zero]
    have hgprod : (∏ j, g j) * (∏ j, (x 0 + y j)) = 1 := by
      rw [hg, ← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun j _ => inv_mul_cancel₀ (hxy 0 j))
    have hhprod : (∏ i, h' i) * (∏ i : Fin n, (x i.succ + y 0)) = 1 := by
      rw [hh', ← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun i _ => inv_mul_cancel₀ (hxy i.succ 0))
    have hdenom : (∏ i, ∏ j, (x i + y j)) =
        (∏ j, (x 0 + y j)) * ((∏ i : Fin n, (x i.succ + y 0)) *
          ∏ i : Fin n, ∏ j : Fin n, (x i.succ + y j.succ)) := by
      rw [Fin.prod_univ_succ]
      congr 1
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => by rw [Fin.prod_univ_succ])
    have hnum : (∏ i, ∏ j ∈ Finset.Ioi i, ((x i - x j) * (y i - y j))) =
        ((∏ j ∈ Finset.Ioi (0 : Fin (n + 1)), (x 0 - x j)) *
          (∏ j ∈ Finset.Ioi (0 : Fin (n + 1)), (y 0 - y j))) *
        ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((x i.succ - x j.succ) * (y i.succ - y j.succ)) := by
      rw [Fin.prod_univ_succ]
      congr 1
      · rw [← Finset.prod_mul_distrib]
      · exact Finset.prod_congr rfl (fun i _ => by rw [Fin.prod_Ioi_succ])
    rw [hdet]
    calc (∏ i, f i) * ((∏ j, g j) * ((∏ i, h' i) * ((∏ j, k' j) *
            (cauchyMatrix (fun i : Fin n => x i.succ) (fun j : Fin n => y j.succ)).det))) *
          ∏ i, ∏ j, (x i + y j)
        = ((∏ i, f i) * (∏ j, k' j)) * (((∏ j, g j) * ∏ j, (x 0 + y j)) *
            (((∏ i, h' i) * ∏ i : Fin n, (x i.succ + y 0)) *
              ((cauchyMatrix (fun i : Fin n => x i.succ) (fun j : Fin n => y j.succ)).det *
                ∏ i : Fin n, ∏ j : Fin n, (x i.succ + y j.succ)))) := by
          rw [hdenom]; ring
      _ = ((∏ i, f i) * (∏ j, k' j)) *
            ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
              ((x i.succ - x j.succ) * (y i.succ - y j.succ)) := by
          rw [hgprod, hhprod, hrec]; ring
      _ = ∏ i, ∏ j ∈ Finset.Ioi i, ((x i - x j) * (y i - y j)) := by
          rw [hnum, hfprod, hkprod]

end GaloisForLFunctions.HTGeometry
