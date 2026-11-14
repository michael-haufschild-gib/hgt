import GaloisForLFunctions.HTGeometry.Arithmetic.IntegralTests
import Mathlib.Tactic.Ring

/-!
# All multipliers preserving square denominators

A rational preserves square denominators under multiplication exactly when
it is a signed integer square. Small inverse prime squares force every
valuation of a preserving multiplier to be even. Testing the integer `p`
then excludes negative valuations. Unique factorization finishes the
classification.
-/

namespace GaloisForLFunctions.HTGeometry.Arithmetic

/-- Multipliers carrying every rational with square denominator to another
rational with square denominator. -/
def PreservesSquareDenominators (q : ℚ) : Prop :=
  ∀ r : ℚ, SquareDenominator r → SquareDenominator (q * r)

private theorem preserving_multiplier_even {q : ℚ} (hq : q ≠ 0)
    (h : PreservesSquareDenominators q) (p : ℕ) [hp : Fact p.Prime] :
    Even (padicValRat p q) := by
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  let k : ℤ := (padicValRat p q).natAbs + 1
  let t : ℚ := (p : ℚ) ^ (-k)
  have ht : t ≠ 0 := zpow_ne_zero _ hpQ
  have htv : padicValRat p t = -k := by
    rw [t, padicValRat.zpow, padicValRat.self hp.out.one_lt, mul_one]
  have htest := (squareDenominator_iff _).mp (h (t ^ 2) (squareDenominator_sq t)) p hp.out
  rw [padicValRat.mul hq (pow_ne_zero 2 ht), padicValRat.pow, htv] at htest
  have hbound := Int.le_natAbs (a := padicValRat p q)
  dsimp only [k] at htest
  rw [Int.even_iff] at htest ⊢
  norm_cast at htest
  omega

private theorem preserving_multiplier_integral {q : ℚ} (hq : q ≠ 0)
    (h : PreservesSquareDenominators q) (p : ℕ) [hp : Fact p.Prime] :
    0 ≤ padicValRat p q := by
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have heven := preserving_multiplier_even hq h p
  have hpD : SquareDenominator (p : ℚ) := by simp [SquareDenominator]
  have htest := (squareDenominator_iff _).mp (h p hpD) p hp.out
  rw [padicValRat.mul hq hpQ, padicValRat.self hp.out.one_lt] at htest
  rw [Int.even_iff] at heven htest
  omega

/-- Integral square multipliers preserve the predicate at every prime. -/
theorem squareDenominator_int_sq_mul (n : ℤ) {r : ℚ} (hr : SquareDenominator r) :
    SquareDenominator ((n : ℚ) ^ 2 * r) := by
  by_cases hn : n = 0
  · simp [hn, squareDenominator_zero]
  by_cases hr0 : r = 0
  · simp [hr0, squareDenominator_zero]
  apply (squareDenominator_iff _).mpr
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  have hnQ : (n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn
  rw [padicValRat.mul (pow_ne_zero 2 hnQ) hr0, padicValRat.pow]
  rcases (squareDenominator_iff r).mp hr p hp with hnonneg | heven
  · left
    have hnval : 0 ≤ padicValRat p (n : ℚ) := by simp
    omega
  · exact Or.inr ((even_two_mul _).add heven)

/-- Complete classification of the multiplicative preservers of the
square-denominator set. -/
theorem preservesSquareDenominators_iff (q : ℚ) :
    PreservesSquareDenominators q ↔
      ∃ n : ℤ, q = (n : ℚ) ^ 2 ∨ q = -(n : ℚ) ^ 2 := by
  constructor
  · intro h
    by_cases hq : q = 0
    · exact ⟨0, Or.inl (by simp [hq])⟩
    have hInt : ∃ n : ℤ, q = n := (forall_prime_squareDenominator_iff_integer q).mp (by
      intro p hp
      letI : Fact p.Prime := ⟨hp⟩
      exact (squareDenominator_prime_mul_sq_iff p q).mpr
        (preserving_multiplier_integral hq h p))
    obtain ⟨n, rfl⟩ := hInt
    have hsquare : IsSquare n.natAbs := (nat_isSquare_iff_prime_valuations_even _).mpr (by
      intro p hp
      letI : Fact p.Prime := ⟨hp⟩
      have heven := preserving_multiplier_even hq h p
      change Even (padicValNat p n.natAbs : ℤ) at heven
      exact (Int.even_coe_nat _).mp heven)
    obtain ⟨a, ha⟩ := hsquare
    refine ⟨(a : ℤ), ?_⟩
    have habs : |n| = (a : ℤ) ^ 2 := by
      rw [← Int.natCast_natAbs, ha, Nat.cast_mul, sq]
    by_cases hn : 0 ≤ n
    · left
      rw [abs_of_nonneg hn] at habs
      exact_mod_cast habs
    · right
      rw [abs_of_neg (lt_of_not_ge hn)] at habs
      have hn' : n = -(a : ℤ) ^ 2 := by omega
      exact_mod_cast hn'
  · rintro ⟨n, h | h⟩ r hr
    · rw [h]
      exact squareDenominator_int_sq_mul n hr
    · rw [h, neg_mul]
      change IsSquare (-((n : ℚ) ^ 2 * r)).den
      rw [Rat.neg_den]
      exact squareDenominator_int_sq_mul n hr

#print axioms preservesSquareDenominators_iff

end GaloisForLFunctions.HTGeometry.Arithmetic
