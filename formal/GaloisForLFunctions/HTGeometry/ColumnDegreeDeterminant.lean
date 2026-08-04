import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# The leading coefficient of a determinant with column-degree bounds

If every entry of the `j`-th column of a matrix of polynomials has degree at most `d j`, then the
determinant has degree at most `∑ d j`, and its coefficient at that degree is the determinant of the
matrix of `d j`-th coefficients.

This generalises the linear-column case: there each column has degree at most one and the extracted
matrix is the matrix of linear parts.  With arbitrary column degrees it is the extraction step of a
Jacobian induction whose columns are polynomial rather than affine in the eliminated variable.

Mathlib has the uniform-degree product statement `Polynomial.coeff_prod_of_natDegree_le`; the
per-index form proved here is what a determinant needs, since different columns carry different
degrees.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {R : Type*} [CommRing R]

/-- **The top coefficient of a product of two polynomials with matching degree bounds.** -/
theorem coeff_mul_of_natDegree_le {p q : Polynomial R} {a b : ℕ}
    (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) :
    (p * q).coeff (a + b) = p.coeff a * q.coeff b := by
  classical
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_single ((a, b) : ℕ × ℕ) ?_ ?_
  · intro x hx hne
    have hxsum : x.1 + x.2 = a + b := Finset.mem_antidiagonal.mp hx
    rcases lt_trichotomy x.1 a with hlt | heq | hgt
    · have hb : b < x.2 := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq hb), mul_zero]
    · exfalso
      refine hne ?_
      have hx2 : x.2 = b := by omega
      exact Prod.ext heq hx2
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hgt), zero_mul]
  · intro hmem
    exact absurd (Finset.mem_antidiagonal.mpr (rfl : (a, b).1 + (a, b).2 = a + b)) hmem

/-- **The top coefficient of a product with per-index degree bounds.** -/
theorem coeff_prod_of_natDegree_le' {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Polynomial R) (d : ι → ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hprod : (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, d i :=
        le_trans (Polynomial.natDegree_prod_le s f)
          (Finset.sum_le_sum fun i hi => h i (Finset.mem_insert_of_mem hi))
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha,
        coeff_mul_of_natDegree_le (h a (Finset.mem_insert_self a s)) hprod,
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

/-- **The leading coefficient of a determinant with column-degree bounds.** -/
theorem coeff_det_of_column_natDegree_le {n : ℕ} {M : Matrix (Fin n) (Fin n) (Polynomial R)}
    {d : Fin n → ℕ} (hdeg : ∀ i j, (M i j).natDegree ≤ d j) :
    M.det.coeff (∑ j, d j) = (Matrix.of fun i j => (M i j).coeff (d j)).det := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Polynomial.coeff_smul]
  congr 1
  exact coeff_prod_of_natDegree_le' Finset.univ (fun i => M (σ i) i) d
    (fun i _ => hdeg (σ i) i)

end GaloisForLFunctions.HTGeometry
