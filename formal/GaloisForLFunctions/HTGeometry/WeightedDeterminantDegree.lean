import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Determinants of polynomial matrices with row and column degree weights

If every entry of a square matrix of polynomials has degree bounded by the sum of a weight of its
row and a weight of its column, the determinant has degree bounded by the sum of all the weights.
Each term of the determinant picks one entry from every row and every column, so the bounds add up
to the same total whichever permutation is taken.

Mathlib bounds a determinant only by the uniform entry degree times the size.  The weighted bound is
what degree estimates for resultants and eliminants need: the Sylvester matrix has entries whose
degrees fall off along the rows, and the uniform bound is far too weak there.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {R : Type*} [CommRing R] {N : ℕ}

/-- **The weighted degree bound for a determinant.** -/
theorem degree_det_le_of_degree_le (M : Matrix (Fin N) (Fin N) R[X]) (u v : Fin N → ℕ)
    (h : ∀ i j, (M i j).degree ≤ (u i : WithBot ℕ) + (v j : WithBot ℕ)) :
    M.det.degree ≤ ((∑ i, u i : ℕ) : WithBot ℕ) + ((∑ j, v j : ℕ) : WithBot ℕ) := by
  classical
  have hsum : ∀ σ : Equiv.Perm (Fin N),
      (∏ i, M (σ i) i).degree
        ≤ ((∑ i, u i : ℕ) : WithBot ℕ) + ((∑ j, v j : ℕ) : WithBot ℕ) := by
    intro σ
    refine le_trans (Polynomial.degree_prod_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun i _ => h (σ i) i) ?_
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ (fun i => (u i : WithBot ℕ))]
    refine add_le_add (le_of_eq ?_) (le_of_eq ?_)
    · exact (Nat.cast_sum Finset.univ u).symm
    · exact (Nat.cast_sum Finset.univ v).symm
  rw [Matrix.det_apply']
  refine le_trans (Polynomial.degree_sum_le _ _) (Finset.sup_le fun σ _ => ?_)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
  · rw [hσ]
    simpa using hsum σ
  · rw [hσ]
    have hne : ((((-1 : ℤˣ) : ℤ) : R[X])) = -1 := by norm_num
    rw [hne, neg_one_mul, Polynomial.degree_neg]
    exact hsum σ

/-- **The weighted degree bound in the form of natural degrees.** -/
theorem natDegree_det_le_of_degree_le (M : Matrix (Fin N) (Fin N) R[X]) (u v : Fin N → ℕ)
    (h : ∀ i j, (M i j).degree ≤ (u i : WithBot ℕ) + (v j : WithBot ℕ)) :
    M.det.natDegree ≤ (∑ i, u i) + (∑ j, v j) := by
  refine Polynomial.natDegree_le_iff_degree_le.2 (le_trans
    (degree_det_le_of_degree_le M u v h) (le_of_eq ?_))
  exact (Nat.cast_add _ _).symm


/-! ## The shifted form, with the row weight decreasing along the rows -/

/-- **The determinant bound when the entry degrees fall off along the rows.**  Writing the bound on
the entry in row `i` and column `j` as `degree + i ≤ c j` absorbs a decreasing row weight without
leaving the natural numbers, which is the shape the Sylvester matrix of two polynomials has. -/
theorem degree_det_add_le (M : Matrix (Fin N) (Fin N) R[X]) (c : Fin N → ℕ)
    (h : ∀ i j, (M i j).degree + (((i : ℕ) : ℕ) : WithBot ℕ) ≤ ((c j : ℕ) : WithBot ℕ)) :
    M.det.degree + ((∑ i : Fin N, (i : ℕ) : ℕ) : WithBot ℕ)
      ≤ ((∑ j, c j : ℕ) : WithBot ℕ) := by
  classical
  have hterm : ∀ σ : Equiv.Perm (Fin N),
      ((((Equiv.Perm.sign σ : ℤ) : R[X])) * ∏ i, M (σ i) i).degree
          + ((∑ i : Fin N, (i : ℕ) : ℕ) : WithBot ℕ)
        ≤ ((∑ j, c j : ℕ) : WithBot ℕ) := by
    intro σ
    have hprod : (∏ i, M (σ i) i).degree + ((∑ i : Fin N, (i : ℕ) : ℕ) : WithBot ℕ)
        ≤ ((∑ j, c j : ℕ) : WithBot ℕ) := by
      have hshift : ((∑ i : Fin N, (i : ℕ) : ℕ) : WithBot ℕ)
          = ∑ i : Fin N, (((σ i : ℕ) : ℕ) : WithBot ℕ) := by
        rw [Equiv.sum_comp σ (fun i => (((i : ℕ) : ℕ) : WithBot ℕ))]
        exact Nat.cast_sum Finset.univ (fun i : Fin N => (i : ℕ))
      calc (∏ i, M (σ i) i).degree + ((∑ i : Fin N, (i : ℕ) : ℕ) : WithBot ℕ)
          ≤ (∑ i, (M (σ i) i).degree) + ((∑ i : Fin N, (i : ℕ) : ℕ) : WithBot ℕ) := by
            gcongr
            exact Polynomial.degree_prod_le _ _
        _ = (∑ i, (M (σ i) i).degree) + ∑ i : Fin N, (((σ i : ℕ) : ℕ) : WithBot ℕ) := by
            rw [hshift]
        _ = ∑ i, ((M (σ i) i).degree + (((σ i : ℕ) : ℕ) : WithBot ℕ)) :=
            (Finset.sum_add_distrib).symm
        _ ≤ ∑ i, ((c i : ℕ) : WithBot ℕ) := Finset.sum_le_sum fun i _ => h (σ i) i
        _ = ((∑ j, c j : ℕ) : WithBot ℕ) := (Nat.cast_sum Finset.univ c).symm
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
    · rw [hσ]
      simpa using hprod
    · rw [hσ]
      have hne : ((((-1 : ℤˣ) : ℤ) : R[X])) = -1 := by norm_num
      rw [hne, neg_one_mul, Polynomial.degree_neg]
      exact hprod
  obtain ⟨σ₀, -, hσ₀⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Equiv.Perm (Fin N)))
    ⟨1, Finset.mem_univ 1⟩
    (fun σ => ((((Equiv.Perm.sign σ : ℤ) : R[X])) * ∏ i, M (σ i) i).degree)
  calc M.det.degree + ((∑ i : Fin N, (i : ℕ) : ℕ) : WithBot ℕ)
      ≤ (Finset.univ.sup fun σ : Equiv.Perm (Fin N) =>
            ((((Equiv.Perm.sign σ : ℤ) : R[X])) * ∏ i, M (σ i) i).degree)
          + ((∑ i : Fin N, (i : ℕ) : ℕ) : WithBot ℕ) := by
        gcongr
        rw [Matrix.det_apply']
        exact Polynomial.degree_sum_le _ _
    _ = ((((Equiv.Perm.sign σ₀ : ℤ) : R[X])) * ∏ i, M (σ₀ i) i).degree
          + ((∑ i : Fin N, (i : ℕ) : ℕ) : WithBot ℕ) := by rw [hσ₀]
    _ ≤ ((∑ j, c j : ℕ) : WithBot ℕ) := hterm σ₀

end GaloisForLFunctions.HTGeometry
