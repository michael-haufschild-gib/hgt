import Mathlib.Data.Nat.Factorization.Basic

/-!
# Prime assembly for Birch--Tate

Birch--Tate is proved prime by prime: Wiles supplies every odd-primary equality and the dyadic
Iwasawa comparison supplies the prime-two equality. This module records the final arithmetic
assembly without hiding either input in a bundled hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Equality of the dyadic valuation and every odd-primary valuation determines a positive natural
number. This is the prime-assembly step in Birch--Tate. -/
theorem nat_eq_of_padicValNat_eq_two_and_odd
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h2 : padicValNat 2 a = padicValNat 2 b)
    (hodd : ∀ p : ℕ, p.Prime → p ≠ 2 → padicValNat p a = padicValNat p b) :
    a = b := by
  rw [Nat.eq_iff_prime_padicValNat_eq a b ha hb]
  intro p hp
  by_cases h : p = 2
  · simpa [h] using h2
  · exact hodd p hp h

end GaloisForLFunctions.HTGeometry
