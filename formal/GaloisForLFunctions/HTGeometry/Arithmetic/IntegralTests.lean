import GaloisForLFunctions.HTGeometry.Arithmetic.SquareDenominator

/-!
# Integral rationals from prime square-denominator tests

The family of tests `D₂(pq²)` detects exactly the embedded integers.
This is an intersection over all primes, not an existential definition of
the integers: each test is an exact semilocal integrality condition.
-/

namespace GaloisForLFunctions.HTGeometry.Arithmetic

/-- Nonnegative rational valuation is exactly absence of the prime from
the reduced denominator. -/
theorem nonneg_val_iff_not_dvd_den (p : ℕ) [hp : Fact p.Prime] (q : ℚ) :
    0 ≤ padicValRat p q ↔ ¬ p ∣ q.den := by
  constructor
  · intro h hd
    have hn : ¬ p ∣ q.num.natAbs := by
      intro hn
      have h := Nat.dvd_gcd hn hd
      rw [q.reduced.gcd_eq_one] at h
      exact hp.out.not_dvd_one h
    have hnum := padicValNat.eq_zero_of_not_dvd hn
    have hden := one_le_padicValNat_of_dvd q.den_nz hd
    change 0 ≤ (padicValNat p q.num.natAbs : ℤ) - padicValNat p q.den at h
    rw [hnum] at h
    omega
  · intro hd
    change 0 ≤ (padicValNat p q.num.natAbs : ℤ) - padicValNat p q.den
    rw [padicValNat.eq_zero_of_not_dvd hd]
    simp

/-- Reduced denominator exponents are the negative parts of the rational
valuations. This includes zero under the total valuation convention. -/
theorem den_valuation_eq_negative_part (p : ℕ) [hp : Fact p.Prime] (q : ℚ) :
    (padicValNat p q.den : ℤ) = max (-padicValRat p q) 0 := by
  by_cases hq : 0 ≤ padicValRat p q
  · have hd := (nonneg_val_iff_not_dvd_den p q).mp hq
    rw [padicValNat.eq_zero_of_not_dvd hd, Nat.cast_zero, max_eq_right (by omega)]
  · have hd : p ∣ q.den := by
      by_contra hd
      exact hq ((nonneg_val_iff_not_dvd_den p q).mpr hd)
    have hn : ¬ p ∣ q.num.natAbs := by
      intro hn
      have h := Nat.dvd_gcd hn hd
      rw [q.reduced.gcd_eq_one] at h
      exact hp.out.not_dvd_one h
    have hnval := padicValNat.eq_zero_of_not_dvd hn
    change (padicValNat p q.den : ℤ) =
      max (-((padicValNat p q.num.natAbs : ℤ) - padicValNat p q.den)) 0
    rw [hnval]
    simp

/-- The intersection of all prime square-denominator tests is exactly `ℤ`. -/
theorem forall_prime_squareDenominator_iff_integer (q : ℚ) :
    (∀ p : ℕ, p.Prime → SquareDenominator ((p : ℚ) * q ^ 2)) ↔
      ∃ n : ℤ, q = n := by
  constructor
  · intro h
    have hd : q.den = 1 := Nat.eq_one_iff_not_exists_prime_dvd.mpr (by
      intro p hp
      letI : Fact p.Prime := ⟨hp⟩
      exact (nonneg_val_iff_not_dvd_den p q).mp
        ((squareDenominator_prime_mul_sq_iff p q).mp (h p hp)))
    exact ⟨q.num, ((Rat.den_eq_one_iff q).mp hd).symm⟩
  · rintro ⟨n, rfl⟩ p hp
    letI : Fact p.Prime := ⟨hp⟩
    apply (squareDenominator_prime_mul_sq_iff p (n : ℚ)).mpr
    simp

/-- A finite collection of prime tests expresses simultaneous integrality
without imposing integrality at the other primes. -/
theorem finite_prime_tests_iff (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (q : ℚ) :
    (∀ p ∈ S, SquareDenominator ((p : ℚ) * q ^ 2)) ↔
      ∀ p ∈ S, ¬ p ∣ q.den := by
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  letI : Fact p.Prime := ⟨hS p hp⟩
  rw [squareDenominator_prime_mul_sq_iff, nonneg_val_iff_not_dvd_den]

end GaloisForLFunctions.HTGeometry.Arithmetic
