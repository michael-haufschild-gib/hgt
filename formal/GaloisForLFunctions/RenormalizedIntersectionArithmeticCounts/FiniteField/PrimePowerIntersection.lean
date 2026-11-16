import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.FiniteField.FrobeniusFixedCardinality
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Exact stabilization of Frobenius intersections along prime-power towers

Intersecting the degree-`n` Frobenius fixed field with the degree-`q^k`
fixed field retains degree `q^min(v_q(n),k)`. Thus the intersection stabilizes
after `v_q(n)` levels, including when the two degrees are not coprime.

This transfers the prime-to-p intersection argument in Lei--Neamti's theta
comparison to the corpus's actual Frobenius fixed subfields. No finiteness of
the ambient field is needed for the subfield identities.
-/

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

/-- The common divisor with a prime power retains exactly the truncated prime valuation. -/
theorem gcd_prime_power_eq_truncated_valuation (q : Nat.Primes) (n k : ℕ) :
    Nat.gcd (n + 1) ((q : ℕ) ^ k) = (q : ℕ) ^ min (padicValNat q (n + 1)) k := by
  obtain ⟨j, hj, hg⟩ := (Nat.dvd_prime_pow q.property).mp
    (Nat.gcd_dvd_right (n + 1) ((q : ℕ) ^ k))
  have hleft := Nat.gcd_dvd_left (n + 1) ((q : ℕ) ^ k)
  rw [hg] at hleft
  have hv := (Nat.pow_dvd_iff_le_padicValNat q.property.ne_one (Nat.succ_ne_zero n)).mp hleft
  have hlow : (q : ℕ) ^ min (padicValNat q (n + 1)) k ∣
      Nat.gcd (n + 1) ((q : ℕ) ^ k) :=
    Nat.dvd_gcd
      ((Nat.pow_dvd_iff_le_padicValNat q.property.ne_one (Nat.succ_ne_zero n)).mpr
        (min_le_left _ _))
      (pow_dvd_pow _ (min_le_right _ _))
  rw [hg] at hlow
  have hl := (Nat.pow_dvd_pow_iff_le_right q.property.one_lt).mp hlow
  rw [hg, le_antisymm (le_min hv hj) hl]

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]

/-- Exact intersection with every level of a prime-power Frobenius tower. -/
theorem frobeniusFixedSubfield_inf_primePower (q : Nat.Primes) (n k : ℕ) :
    frobeniusFixedSubfield p K (n + 1) ⊓ frobeniusFixedSubfield p K ((q : ℕ) ^ k) =
      frobeniusFixedSubfield p K ((q : ℕ) ^ min (padicValNat q (n + 1)) k) := by
  rw [frobeniusFixedSubfield_inf, gcd_prime_power_eq_truncated_valuation]

/-- Every level beyond the prime valuation has exactly the same intersection. -/
theorem frobeniusFixedSubfield_primePower_stabilizes (q : Nat.Primes) (n k : ℕ) :
    frobeniusFixedSubfield p K (n + 1) ⊓
        frobeniusFixedSubfield p K ((q : ℕ) ^ (padicValNat q (n + 1) + k)) =
      frobeniusFixedSubfield p K ((q : ℕ) ^ padicValNat q (n + 1)) := by
  rw [frobeniusFixedSubfield_inf_primePower, min_eq_left (Nat.le_add_right _ _)]

/-- The stable intersection is already reached at the valuation level. -/
theorem frobeniusFixedSubfield_primePower_stable_level (q : Nat.Primes) (n k : ℕ) :
    frobeniusFixedSubfield p K (n + 1) ⊓
        frobeniusFixedSubfield p K ((q : ℕ) ^ (padicValNat q (n + 1) + k)) =
      frobeniusFixedSubfield p K (n + 1) ⊓
        frobeniusFixedSubfield p K ((q : ℕ) ^ padicValNat q (n + 1)) := by
  rw [frobeniusFixedSubfield_primePower_stabilizes,
    frobeniusFixedSubfield_inf_primePower, min_self]

/-- Over a finite ambient field the intersection size includes its exact ambient-degree cutoff. -/
theorem frobeniusFixedSubfield_inf_primePower_card [Finite K] [Algebra (ZMod p) K]
    (q : Nat.Primes) (n k : ℕ) :
    Nat.card ↥(frobeniusFixedSubfield p K (n + 1) ⊓
      frobeniusFixedSubfield p K ((q : ℕ) ^ k)) =
      p ^ Nat.gcd (Module.finrank (ZMod p) K)
        ((q : ℕ) ^ min (padicValNat q (n + 1)) k) := by
  rw [frobeniusFixedSubfield_inf_primePower, frobeniusFixedSubfield_card]

#print axioms gcd_prime_power_eq_truncated_valuation
#print axioms frobeniusFixedSubfield_primePower_stabilizes
#print axioms frobeniusFixedSubfield_inf_primePower_card

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
