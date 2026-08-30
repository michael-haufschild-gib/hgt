import Mathlib

/-!
# The Hankel determinant has total degree at most its size

Expanding a `d × d` determinant over permutations gives a sum of products of exactly `d` entries,
so as a polynomial in the entries `P_k` of a Hankel matrix it has total degree at most `d`: every
monomial of the reducibility condition carries combination-mode support at most `d`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-- **Bounded combination-mode support.**  The determinant of the `d × d` Hankel matrix in the
indeterminates `X₀, X₁, …` has total degree at most `d`. -/
theorem totalDegree_hankelDet_le {R : Type*} [CommRing R] [Nontrivial R] (d : ℕ) :
    (Matrix.det (fun i j : Fin d =>
      (MvPolynomial.X (i.val + j.val) : MvPolynomial ℕ R))).totalDegree ≤ d := by
  classical
  rw [Matrix.det_apply']
  refine MvPolynomial.totalDegree_finsetSum_le fun σ _ => ?_
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  have hconst : ((((Equiv.Perm.sign σ : ℤˣ) : ℤ)) : MvPolynomial ℕ R).totalDegree = 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  rw [hconst, zero_add]
  refine le_trans (MvPolynomial.totalDegree_finsetProd _ _) (le_of_eq ?_)
  calc ∑ i : Fin d, (MvPolynomial.X ((σ i).val + i.val) : MvPolynomial ℕ R).totalDegree
      = ∑ _i : Fin d, 1 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact MvPolynomial.totalDegree_X _
    _ = d := by simp

end GaloisForLFunctions.HTGeometry
