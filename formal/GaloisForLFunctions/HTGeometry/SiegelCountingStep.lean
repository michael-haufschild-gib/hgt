import GaloisForLFunctions.HTGeometry.KernelOfDimensionDrop
import GaloisForLFunctions.HTGeometry.MultiIndexCounts
import GaloisForLFunctions.HTGeometry.SiegelDegreeCount

/-!
# The counting step of a Siegel-type argument

A linear map from the coefficient space of polynomials whose exponents are all at most `m` in
`n + 1` variables into the space of Taylor conditions — one for each of finitely many centres and
each multi-index of total degree below `N` in `n` variables — has a nonzero kernel vector as soon as

`(number of centres) · N ^ n < (m + 1) ^ (n + 1)`.

The source has exactly `(m + 1) ^ (n + 1)` dimensions and the target at most
`(number of centres) · N ^ n`, by the two multi-index counts.

Combined with `siegel_count_lt`, which supplies the inequality for every large `m` once `N` grows
only linearly in `m`, this is the step that produces the nonzero polynomial a Siegel bound feeds to
the Schwarz estimate.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {ι : Type*} [Fintype ι] {n m N : ℕ}

theorem finrank_coeffSpace :
    finrank ℂ ((Fin (n + 1) → Fin (m + 1)) → ℂ) = (m + 1) ^ (n + 1) := by
  rw [finrank_fintype_fun_eq_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

theorem finrank_conditionSpace (S : Finset (Fin n → ℕ)) :
    finrank ℂ ((ι × S) → ℂ) = Fintype.card ι * S.card := by
  rw [finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_coe]

/-- **The counting step.**  Too many coefficients for too few Taylor conditions produce a nonzero
kernel vector. -/
theorem exists_ne_zero_of_siegel_count (S : Finset (Fin n → ℕ))
    (hS : ∀ β ∈ S, ∑ i, β i < N)
    (T : ((Fin (n + 1) → Fin (m + 1)) → ℂ) →ₗ[ℂ] ((ι × S) → ℂ))
    (hcount : Fintype.card ι * N ^ n < (m + 1) ^ (n + 1)) :
    ∃ a : (Fin (n + 1) → Fin (m + 1)) → ℂ, a ≠ 0 ∧ T a = 0 := by
  refine exists_ne_zero_apply_eq_zero_of_finrank_lt T ?_
  rw [finrank_coeffSpace, finrank_conditionSpace]
  refine lt_of_le_of_lt ?_ hcount
  exact Nat.mul_le_mul_left _ (card_le_pow_of_sum_lt S hS)

/-- **The counting step, with the degree supplied by the arithmetic.**  For every large degree the
count closes, so a nonzero kernel vector exists. -/
theorem exists_ne_zero_of_siegel_count_of_large {K A : ℕ} (hn : 1 ≤ n)
    (hK : Fintype.card ι ≤ K) (hm : K * A ^ n < m) (hN : N ≤ A * m)
    (S : Finset (Fin n → ℕ)) (hS : ∀ β ∈ S, ∑ i, β i < N)
    (T : ((Fin (n + 1) → Fin (m + 1)) → ℂ) →ₗ[ℂ] ((ι × S) → ℂ)) :
    ∃ a : (Fin (n + 1) → Fin (m + 1)) → ℂ, a ≠ 0 ∧ T a = 0 := by
  refine exists_ne_zero_of_siegel_count S hS T ?_
  refine lt_of_le_of_lt ?_ (siegel_count_lt (K := K) (A := A) hn hm)
  exact Nat.mul_le_mul hK (Nat.pow_le_pow_left hN n)

end GaloisForLFunctions.HTGeometry
