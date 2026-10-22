import GaloisForLFunctions.RHTower.Sieve.PowerSumAffineEquivalence

/-!
# Translation invariance of equal power sums

In any commutative ring, two families `u, v : Fin b → R` with equal power sums
`∑ u_i^j = ∑ v_i^j` for `1 ≤ j ≤ k` keep equal power sums of the same orders after translating
every entry by a common constant `c`. The proof expands `(u_i + c)^j` by the binomial theorem.

## Main results

- `sum_translate_pow_eq_of_powerSums_eq`: equal power sums of orders `1..k` imply
  `∑ (u_i + c)^j = ∑ (v_i + c)^j` for `1 ≤ j ≤ k`.

## Hypotheses

Unconditional algebraic identity; the only premise is the equality of the power sums of orders
`1` through `k`.
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- In a commutative ring, if `∑ u_i^j = ∑ v_i^j` for `1 ≤ j ≤ k`, then
`∑ (u_i + c)^j = ∑ (v_i + c)^j` for `1 ≤ j ≤ k`. -/
theorem sum_translate_pow_eq_of_powerSums_eq
    {R : Type*} [CommRing R] {b k : ℕ} (c : R)
    (u v : Fin b → R)
    (hpower : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∑ i : Fin b, u i ^ j = ∑ i : Fin b, v i ^ j) :
    ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∑ i : Fin b, (u i + c) ^ j =
        ∑ i : Fin b, (v i + c) ^ j := by
  intro j hjpos hjk
  simp_rw [add_pow]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  have hmle : m ≤ j := by simpa using hm
  by_cases hm0 : m = 0
  · subst m
    simp
  · have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have h := hpower m hmpos (hmle.trans hjk)
    calc
      (∑ i : Fin b, u i ^ m * c ^ (j - m) * (j.choose m : R)) =
          (c ^ (j - m) * (j.choose m : R)) * ∑ i : Fin b, u i ^ m := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (c ^ (j - m) * (j.choose m : R)) * ∑ i : Fin b, v i ^ m := by rw [h]
      _ = ∑ i : Fin b, v i ^ m * c ^ (j - m) * (j.choose m : R) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring

end

end RHTower.Sieve

