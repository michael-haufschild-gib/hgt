import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerParameterFields
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.FiniteField.PrimePowerIntersection

/-!
# The exact dyadic cutoff for auxiliary Kummer Frobenius

In the square field of order `p^(2m)`, restrict the middle Frobenius to
the `p^(q^k)`-fixed field. It is nontrivial precisely when `q = 2` and
`k > v₂(m)`. Odd prime towers therefore stay inside the fixed field;
the dyadic tower detects the involution exactly beyond this cutoff.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

private theorem prime_valuation_two (q : Nat.Primes) :
    padicValNat q 2 = if (q : ℕ) = 2 then 1 else 0 := by
  split_ifs with h
  · rw [h, padicValNat.self Nat.prime_two.one_lt]
  · apply padicValNat.eq_zero_of_not_dvd
    intro hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact q.property.ne_one h1
    · exact h h2

private theorem gcd_double_prime_power (q : Nat.Primes) (n k : ℕ) :
    Nat.gcd (2 * (n + 1)) ((q : ℕ) ^ k) =
      (q : ℕ) ^ min (padicValNat q 2 + padicValNat q (n + 1)) k := by
  letI : Fact (Nat.Prime (q : ℕ)) := ⟨q.property⟩
  have h := gcd_prime_power_eq_truncated_valuation q (2 * n + 1) k
  have he : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
  rw [he, padicValNat.mul (by omega) (Nat.succ_ne_zero n)] at h
  exact h

variable (p : ℕ) [Fact p.Prime]

/-- Identity of the restricted Frobenius is equivalent to equality of its two gcd degrees. -/
theorem kummerAuxiliaryFrobenius_eq_id_iff (s k : ℕ) :
    kummerAuxiliaryFrobenius p s k = RingHom.id _ ↔
      Nat.gcd (2 * (s + 1)) k = Nat.gcd (s + 1) k := by
  constructor
  · intro he
    by_contra hn
    obtain ⟨x, hx⟩ := kummerAuxiliaryFrobenius_nontrivial p s k hn
    exact hx (by rw [he]; rfl)
  · exact kummerAuxiliaryFrobenius_eq_id p s k

/-- Only a dyadic tower can detect the middle Frobenius, and only beyond `v₂(s+1)`. -/
theorem kummerAuxiliaryFrobenius_primePower_eq_id_iff (q : Nat.Primes) (s k : ℕ) :
    kummerAuxiliaryFrobenius p s ((q : ℕ) ^ k) = RingHom.id _ ↔
      (q : ℕ) ≠ 2 ∨ k ≤ padicValNat q (s + 1) := by
  rw [kummerAuxiliaryFrobenius_eq_id_iff, gcd_double_prime_power,
    gcd_prime_power_eq_truncated_valuation,
    (Nat.pow_right_injective q.property.one_lt).eq_iff, prime_valuation_two]
  by_cases hq : (q : ℕ) = 2
  · simp only [hq, ↓reduceIte, ne_eq, not_true_eq_false, false_or]
    omega
  · simp only [hq, ↓reduceIte, zero_add, ne_eq, not_false_eq_true, true_or]

/-- A nonfixed auxiliary parameter exists exactly beyond the dyadic cutoff. -/
theorem kummerAuxiliaryFrobenius_primePower_nontrivial_iff (q : Nat.Primes) (s k : ℕ) :
    (∃ x : KummerAuxiliaryField p s ((q : ℕ) ^ k),
      kummerAuxiliaryFrobenius p s ((q : ℕ) ^ k) x ≠ x) ↔
      (q : ℕ) = 2 ∧ padicValNat q (s + 1) < k := by
  have hn : (∃ x : KummerAuxiliaryField p s ((q : ℕ) ^ k),
      kummerAuxiliaryFrobenius p s ((q : ℕ) ^ k) x ≠ x) ↔
      kummerAuxiliaryFrobenius p s ((q : ℕ) ^ k) ≠ RingHom.id _ := by
    constructor
    · rintro ⟨x, hx⟩ he
      exact hx (by rw [he]; rfl)
    · intro he
      by_contra hx
      push Not at hx
      exact he (RingHom.ext hx)
  rw [hn, ne_eq, kummerAuxiliaryFrobenius_primePower_eq_id_iff]
  simp only [not_or, not_not, not_le]

/-- The auxiliary field degree along a prime tower has the exact truncated valuation. -/
theorem kummerAuxiliaryField_primePower_card (q : Nat.Primes) (s k : ℕ) :
    Nat.card (KummerAuxiliaryField p s ((q : ℕ) ^ k)) =
      p ^ ((q : ℕ) ^ min (padicValNat q 2 + padicValNat q (s + 1)) k) := by
  rw [kummerAuxiliaryField_card, gcd_double_prime_power]

/-- The fixed parameters stabilize one dyadic level before the whole auxiliary field. -/
theorem kummerAuxiliaryFixed_primePower_card (q : Nat.Primes) (s k : ℕ) :
    Nat.card ((kummerAuxiliaryFrobenius p s ((q : ℕ) ^ k)).eqLocusField (RingHom.id _)) =
      p ^ ((q : ℕ) ^ min (padicValNat q (s + 1)) k) := by
  rw [kummerAuxiliaryFixed_card, gcd_prime_power_eq_truncated_valuation]

#print axioms kummerAuxiliaryFrobenius_primePower_eq_id_iff
#print axioms kummerAuxiliaryFrobenius_primePower_nontrivial_iff
#print axioms kummerAuxiliaryField_primePower_card
#print axioms kummerAuxiliaryFixed_primePower_card

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
