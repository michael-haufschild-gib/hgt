import Mathlib

/-!
# Cauchy–Binet, permutation-symmetrised

mathlib has `Matrix.det_mul` for square factors but no Cauchy–Binet formula for a rectangular
product `A · B` with `A : m × N` and `B : N × m`.  This file supplies it in the form that avoids the
increasing-enumeration bookkeeping: summing the products of corresponding maximal minors over **all**
index functions `f : Fin m → Fin N` counts each `m`-element index set exactly `m!` times (the
non-injective `f` contribute zero, since both minors then have a repeated row/column), so

`m! · det (A · B) = Σ_{f : Fin m → Fin N} det (A ∘ f) · det (f ∘ B)`.

No division is used, so the identity holds over an arbitrary commutative ring.

## Main results

* `det_eq_sum_perm_row` — the determinant as a permutation sum in the `M i (σ i)` convention;
* `det_mul_eq_sum_fun` — the expansion of `det (A · B)` over index functions;
* `factorial_mul_det_mul` — the symmetrised Cauchy–Binet identity.
-/

namespace GaloisForLFunctions

open Matrix Equiv Finset

variable {R : Type*} [CommRing R] {m N : ℕ}

/-- The determinant as a permutation sum in the `M i (σ i)` convention. -/
theorem det_eq_sum_perm_row {n : Type*} [DecidableEq n] [Fintype n] (M : Matrix n n R) :
    M.det = ∑ σ : Perm n, (Perm.sign σ : R) * ∏ i, M i (σ i) := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

/-- **Expansion of a rectangular product determinant over all index functions.** -/
theorem det_mul_eq_sum_fun (A : Matrix (Fin m) (Fin N) R) (B : Matrix (Fin N) (Fin m) R) :
    (A * B).det = ∑ f : Fin m → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det := by
  classical
  rw [det_eq_sum_perm_row]
  have h1 : ∀ σ : Perm (Fin m), (∏ a, (A * B) a (σ a))
      = ∑ f : Fin m → Fin N, ∏ a, (A a (f a) * B (f a) (σ a)) := by
    intro σ
    simp only [Matrix.mul_apply]
    rw [Finset.prod_univ_sum]
    exact Finset.sum_congr (by rw [Fintype.piFinset_univ]) (fun f _ => rfl)
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [det_eq_sum_perm_row, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.submatrix_apply, id_eq, Finset.prod_mul_distrib]
  ring

/-- Precomposition with the inverse of a permutation, as a bijection of index functions. -/
def arrowPermEquiv (τ : Perm (Fin m)) : (Fin m → Fin N) ≃ (Fin m → Fin N) where
  toFun h := h ∘ (τ.symm : Fin m → Fin m)
  invFun h := h ∘ (τ : Fin m → Fin m)
  left_inv h := by funext a; simp
  right_inv h := by funext a; simp

/-- **Cauchy–Binet, permutation-symmetrised form.**  Summing the products of corresponding maximal
minors over *all* index functions (not only the increasing ones) counts each index set `m!` times;
the non-injective functions contribute zero. -/
theorem factorial_mul_det_mul (A : Matrix (Fin m) (Fin N) R) (B : Matrix (Fin N) (Fin m) R) :
    ((Nat.factorial m : ℕ) : R) * (A * B).det
      = ∑ f : Fin m → Fin N, (A.submatrix id f).det * (B.submatrix f id).det := by
  classical
  have key : ∀ τ : Perm (Fin m),
      (∑ f : Fin m → Fin N,
        (Perm.sign τ : R) * (∏ a, A a (f (τ a))) * (B.submatrix f id).det) = (A * B).det := by
    intro τ
    have hre := (Equiv.sum_comp (arrowPermEquiv (N := N) τ)
      (fun f : Fin m → Fin N =>
        (Perm.sign τ : R) * (∏ a, A a (f (τ a))) * (B.submatrix f id).det))
    rw [← hre, det_mul_eq_sum_fun]
    refine Finset.sum_congr rfl fun h _ => ?_
    have h1 : ∀ a : Fin m, (arrowPermEquiv (N := N) τ h) (τ a) = h a := by
      intro a
      show h (τ.symm (τ a)) = h a
      rw [Equiv.symm_apply_apply]
    have h2 : (B.submatrix (arrowPermEquiv (N := N) τ h) id)
        = (B.submatrix h id).submatrix (τ.symm : Fin m → Fin m) id := by
      ext a b
      rfl
    rw [Finset.prod_congr rfl (fun a _ => by rw [h1 a]), h2, Matrix.det_permute]
    have hsgn : ((Perm.sign τ : ℤ) : R) * ((Perm.sign τ.symm : ℤ) : R) = 1 := by
      rw [Equiv.Perm.sign_symm]
      rcases Int.units_eq_one_or (Perm.sign τ) with h | h <;> rw [h] <;> norm_num
    calc (Perm.sign τ : R) * (∏ a, A a (h a))
            * (((Perm.sign τ.symm : ℤ) : R) * (B.submatrix h id).det)
        = (((Perm.sign τ : ℤ) : R) * ((Perm.sign τ.symm : ℤ) : R))
            * ((∏ a, A a (h a)) * (B.submatrix h id).det) := by ring
      _ = (∏ a, A a (h a)) * (B.submatrix h id).det := by rw [hsgn, one_mul]
  have hRHS : (∑ f : Fin m → Fin N, (A.submatrix id f).det * (B.submatrix f id).det)
      = ∑ τ : Perm (Fin m), ∑ f : Fin m → Fin N,
          (Perm.sign τ : R) * (∏ a, A a (f (τ a))) * (B.submatrix f id).det := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [det_eq_sum_perm_row, Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Matrix.submatrix_apply, id_eq]
  rw [hRHS]
  rw [Finset.sum_congr rfl (fun τ _ => key τ)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

end GaloisForLFunctions
