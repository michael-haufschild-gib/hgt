import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.Tactic

/-!
# Jacobi's formula for a derivation

Over a differential ring the determinant differentiates column by column,

```
(det M)′ = ∑ k, det (M with column k replaced by its derivative),
```

and for an invertible matrix over a differential field this is the logarithmic form

```
(det S)′ / det S = tr (S⁻¹ · S′),
```

so the trace of the logarithmic connection is the logarithmic derivative of the determinant.

The proof is the Leibniz rule applied inside the permutation expansion of the determinant: the
derivative of the product over a permutation is the sum over which factor is differentiated, and
exchanging the two summations regroups the terms as determinants with one column replaced.
-/

open scoped Differential
open Matrix

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] [Differential R]

/-- **Leibniz rule over a finite product.** -/
private theorem deriv_finsetProd {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → R) :
    (∏ i ∈ s, f i)′ = ∑ i ∈ s, (f i)′ * ∏ j ∈ s.erase i, f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hrhs : ∑ i ∈ insert a s, (f i)′ * ∏ j ∈ (insert a s).erase i, f j =
          (f a)′ * ∏ j ∈ s, f j + ∑ i ∈ s, (f i)′ * (f a * ∏ j ∈ s.erase i, f j) := by
        rw [Finset.sum_insert ha, Finset.erase_insert ha]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        have hai : a ≠ i := fun h => ha (h ▸ hi)
        rw [Finset.erase_insert_of_ne hai,
          Finset.prod_insert fun hmem => ha (Finset.mem_of_mem_erase hmem)]
      have hL : (f a • ∑ i ∈ s, (f i)′ * ∏ j ∈ s.erase i, f j) =
          ∑ i ∈ s, (f i)′ * (f a * ∏ j ∈ s.erase i, f j) := by
        rw [smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.prod_insert ha, Differential.deriv.leibniz, ih, hrhs, hL, smul_eq_mul]
      ring

/-- The derivative of a matrix, entrywise. -/
def matrixDeriv {m n : Type*} (M : Matrix m n R) : Matrix m n R := fun i j => (M i j)′

@[simp]
theorem matrixDeriv_apply {m n : Type*} (M : Matrix m n R) (i : m) (j : n) :
    matrixDeriv M i j = (M i j)′ := rfl

/-- **Jacobi's formula.**  The determinant differentiates one column at a time. -/
private theorem deriv_det {n : Type*} [DecidableEq n] [Fintype n] (M : Matrix n n R) :
    (M.det)′ = ∑ k, (M.updateCol k (fun a => (M a k)′)).det := by
  classical
  have hleft : (M.det)′ =
      ∑ σ : Equiv.Perm n, ∑ k : n,
        (Equiv.Perm.sign σ : ℤ) • ((M (σ k) k)′ * ∏ i ∈ Finset.univ.erase k, M (σ i) i) := by
    rw [Matrix.det_apply, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, map_zsmul, deriv_finsetProd, Finset.smul_sum]
  have hright : ∀ k : n, (M.updateCol k (fun a => (M a k)′)).det =
      ∑ σ : Equiv.Perm n,
        (Equiv.Perm.sign σ : ℤ) • ((M (σ k) k)′ * ∏ i ∈ Finset.univ.erase k, M (σ i) i) := by
    intro k
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def]
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
    congr 1
    · rw [Matrix.updateCol_apply, if_pos rfl]
    · refine Finset.prod_congr rfl fun i hi => ?_
      rw [Matrix.updateCol_apply, if_neg (Finset.ne_of_mem_erase hi)]
  rw [hleft, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => (hright k).symm

/-! ### The logarithmic form -/

variable {E : Type*} [Field E] [Differential E]

/-- **Trace of the logarithmic connection.**  For an invertible matrix over a differential field,
the trace of `S⁻¹ · S′` is the logarithmic derivative of the determinant. -/
theorem trace_inv_mul_matrixDeriv {n : Type*} [DecidableEq n] [Fintype n]
    (S : Matrix n n E) (hS : IsUnit S.det) :
    Matrix.trace (S⁻¹ * matrixDeriv S) = (S.det)′ / S.det := by
  have hdet : S.det ≠ 0 := hS.ne_zero
  have hcol : ∀ k : n, (S.updateCol k (fun a => (S a k)′)).det =
      S.det * (S⁻¹ * matrixDeriv S) k k := by
    intro k
    rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, matrixDeriv_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    field_simp
  rw [Matrix.trace, eq_div_iff hdet, Finset.sum_mul]
  rw [deriv_det]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hcol k, Matrix.diag_apply]
  ring

end GaloisForLFunctions.HTGeometry
