import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Square denominators and local integrality

A rational has square reduced denominator exactly when none of its negative
prime valuations is odd. Multiplying a rational square by a prime therefore
tests integrality at that prime, without restricting any other prime.
-/

namespace GaloisForLFunctions.HTGeometry.Arithmetic

/-- The reduced denominator of a rational is a square. -/
def SquareDenominator (q : ℚ) : Prop := IsSquare q.den

private theorem nat_square_iff_even_valuations (n : ℕ) :
    IsSquare n ↔ ∀ p : ℕ, p.Prime → Even (padicValNat p n) := by
  constructor
  · rintro ⟨a, rfl⟩ p hp
    letI : Fact p.Prime := ⟨hp⟩
    rw [← sq, padicValNat.pow]
    exact even_two_mul _
  · intro h
    by_cases hn : n = 0
    · simp [hn]
    refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
    rw [← sq, ← Finset.prod_pow]
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
    apply Finset.prod_congr rfl
    intro p hp
    have he := h p (Nat.prime_of_mem_primeFactors hp)
    rw [← Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp),
      even_iff_exists_two_mul] at he
    obtain ⟨k, hk⟩ := he
    rw [hk, Nat.mul_div_cancel_left _ two_pos, ← pow_mul, mul_comm k 2]

/-- Coprimality of numerator and denominator turns the valuation test into
an exact test on the denominator exponent. -/
theorem even_den_valuation_iff (p : ℕ) [hp : Fact p.Prime] (q : ℚ) :
    Even (padicValNat p q.den) ↔
      0 ≤ padicValRat p q ∨ Even (padicValRat p q) := by
  by_cases hd : p ∣ q.den
  · have hn : ¬ p ∣ q.num.natAbs := by
      intro hn
      have h := Nat.dvd_gcd hn hd
      rw [q.reduced.gcd_eq_one] at h
      exact hp.out.not_dvd_one h
    have hnum := padicValNat.eq_zero_of_not_dvd hn
    have hden := one_le_padicValNat_of_dvd q.den_nz hd
    change Even (padicValNat p q.den) ↔
      0 ≤ (padicValNat p q.num.natAbs : ℤ) - padicValNat p q.den ∨
        Even ((padicValNat p q.num.natAbs : ℤ) - padicValNat p q.den)
    rw [hnum]
    simp only [Nat.cast_zero, zero_sub, Nat.even_iff, Int.even_iff]
    omega
  · have hden := padicValNat.eq_zero_of_not_dvd hd
    change Even (padicValNat p q.den) ↔
      0 ≤ (padicValNat p q.num.natAbs : ℤ) - padicValNat p q.den ∨
        Even ((padicValNat p q.num.natAbs : ℤ) - padicValNat p q.den)
    simp [hden]

/-- The square-denominator predicate is exactly exclusion of negative odd
valuations, including at the prime two. -/
theorem squareDenominator_iff (q : ℚ) :
    SquareDenominator q ↔ ∀ p : ℕ, p.Prime →
      0 ≤ padicValRat p q ∨ Even (padicValRat p q) := by
  rw [SquareDenominator, nat_square_iff_even_valuations]
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  letI : Fact p.Prime := ⟨hp⟩
  exact even_den_valuation_iff p q

@[simp] theorem squareDenominator_zero : SquareDenominator 0 := by
  exact ⟨1, by simp⟩

/-- Every rational square has square reduced denominator. -/
theorem squareDenominator_sq (q : ℚ) : SquareDenominator (q ^ 2) := by
  exact ⟨q.den, by rw [Rat.den_pow, sq]⟩

/-- A prime times a square has an admissible valuation precisely when the
unsquared rational is integral at that prime. -/
theorem prime_mul_sq_local_iff (p : ℕ) [hp : Fact p.Prime] (q : ℚ) :
    (0 ≤ padicValRat p ((p : ℚ) * q ^ 2) ∨
      Even (padicValRat p ((p : ℚ) * q ^ 2))) ↔ 0 ≤ padicValRat p q := by
  by_cases hq : q = 0
  · simp [hq]
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  rw [padicValRat.mul hpQ (pow_ne_zero 2 hq), padicValRat.self hp.out.one_lt,
    padicValRat.pow, Int.even_iff]
  norm_cast
  omega

/-- A single square-denominator condition tests integrality at one chosen
prime and imposes no conditions at other primes. -/
theorem squareDenominator_prime_mul_sq_iff (p : ℕ) [hp : Fact p.Prime] (q : ℚ) :
    SquareDenominator ((p : ℚ) * q ^ 2) ↔ 0 ≤ padicValRat p q := by
  constructor
  · intro h
    exact (prime_mul_sq_local_iff p q).mp ((squareDenominator_iff _).mp h p hp.out)
  · intro h
    by_cases hq : q = 0
    · simp [hq, squareDenominator_zero]
    apply (squareDenominator_iff _).mpr
    intro r hr
    letI : Fact r.Prime := ⟨hr⟩
    by_cases hrp : r = p
    · subst r
      exact (prime_mul_sq_local_iff p q).mpr h
    · have hnd : ¬ r ∣ p := fun hd =>
        hrp ((hp.out.dvd_iff_eq hr.ne_one).mp hd).symm
      have hv : padicValRat r (p : ℚ) = 0 := by
        rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd, Nat.cast_zero]
      have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
      rw [padicValRat.mul hpQ (pow_ne_zero 2 hq), hv, zero_add, padicValRat.pow]
      exact Or.inr (even_two_mul (padicValRat r q))

/-- Dividing a square by an odd prime power tests arbitrary integral
precision at that prime. The zero rational satisfies every precision test. -/
theorem squareDenominator_div_prime_odd_pow_iff
    (p : ℕ) [hp : Fact p.Prime] (q : ℚ) (k : ℕ) :
    SquareDenominator (q ^ 2 / (p : ℚ) ^ (2 * k + 1)) ↔
      q = 0 ∨ (k : ℤ) + 1 ≤ padicValRat p q := by
  by_cases hq : q = 0
  · simp [hq, squareDenominator_zero]
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hv (r : ℕ) [Fact r.Prime] :
      padicValRat r (q ^ 2 / (p : ℚ) ^ (2 * k + 1)) =
        2 * padicValRat r q - (2 * (k : ℤ) + 1) * padicValRat r p := by
    rw [padicValRat.div (pow_ne_zero 2 hq) (pow_ne_zero _ hpQ),
      padicValRat.pow, padicValRat.pow]
    push_cast
    rfl
  rw [or_iff_right hq, squareDenominator_iff]
  constructor
  · intro h
    have h := h p hp.out
    rw [hv, padicValRat.self hp.out.one_lt, mul_one, Int.even_iff] at h
    omega
  · intro h r hr
    letI : Fact r.Prime := ⟨hr⟩
    rw [hv]
    by_cases hrp : r = p
    · subst r
      rw [padicValRat.self hp.out.one_lt, mul_one]
      exact Or.inl (by omega)
    · have hnd : ¬ r ∣ p := fun hd =>
        hrp ((hp.out.dvd_iff_eq hr.ne_one).mp hd).symm
      rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd,
        Nat.cast_zero, mul_zero, sub_zero]
      exact Or.inr (even_two_mul _)

end GaloisForLFunctions.HTGeometry.Arithmetic
