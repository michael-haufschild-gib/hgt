import GaloisForLFunctions.RHTower.Sieve.OmegaMGF

/-!+# Exact Bonferroni remainders for avoidance counts

An even truncation of the avoidance indicator has error at most the next factorial
moment. The adjacent odd truncation proves this without independence assumptions.
For small-prime divisibility, the error is an exact sum over one level of divisors.
-/

open Finset
open RHTower.Sieve

namespace GaloisForLFunctions.BezoutValuationIncidence.Sieve

/-- The gap between an even Bonferroni majorant and the avoidance indicator is bounded
by the first omitted binomial coefficient. -/
theorem bonferroni_one_bounds (w r : ℕ) :
    (if w = 0 then (1 : ℝ) else 0) ≤ binomialPartial 1 w (2 * r) ∧
      binomialPartial 1 w (2 * r) ≤
        (if w = 0 then (1 : ℝ) else 0) + (w.choose (2 * r + 1) : ℝ) := by
  have heven := binomialPartial_sign (x := 1) (by norm_num) (by norm_num) w (2 * r)
  have hodd := binomialPartial_sign (x := 1) (by norm_num) (by norm_num) w (2 * r + 1)
  have hpow : (1 - 1 : ℝ) ^ w = if w = 0 then 1 else 0 := by
    by_cases hw : w = 0 <;> simp [hw]
  have hstep : binomialPartial 1 w (2 * r + 1) =
      binomialPartial 1 w (2 * r) - (w.choose (2 * r + 1) : ℝ) := by
    unfold binomialPartial
    rw [sum_range_succ]
    simp only [pow_add, pow_mul]
    norm_num
    ring
  rw [hpow] at heven hodd
  norm_num [pow_add, pow_mul] at heven hodd
  rw [hstep] at hodd
  constructor <;> linarith only [heven, hodd]

/-- Arbitrary finite event counts inherit the same exact factorial-moment remainder. -/
theorem sum_bonferroni_error {α : Type*} (X : Finset α) (w : α → ℕ) (r : ℕ) :
    0 ≤ (∑ x ∈ X, binomialPartial 1 (w x) (2 * r)) -
        ((X.filter fun x => w x = 0).card : ℝ) ∧
      (∑ x ∈ X, binomialPartial 1 (w x) (2 * r)) -
        ((X.filter fun x => w x = 0).card : ℝ) ≤
          ∑ x ∈ X, ((w x).choose (2 * r + 1) : ℝ) := by
  classical
  rw [natCast_card_filter]
  have hlo := sum_le_sum (s := X) (fun x _ => (bonferroni_one_bounds (w x) r).1)
  have hhi := sum_le_sum (s := X) (fun x _ => (bonferroni_one_bounds (w x) r).2)
  rw [sum_add_distrib] at hhi
  constructor <;> linarith only [hlo, hhi]

/-- For rough-number sieves, the Bonferroni remainder is bounded by one explicit divisor level. -/
theorem omegaSmall_bonferroni_error (z a b r : ℕ) :
    0 ≤ (∑ n ∈ Ioc a b, binomialPartial 1 (omegaSmall z n) (2 * r)) -
        (((Ioc a b).filter fun n => omegaSmall z n = 0).card : ℝ) ∧
      (∑ n ∈ Ioc a b, binomialPartial 1 (omegaSmall z n) (2 * r)) -
        (((Ioc a b).filter fun n => omegaSmall z n = 0).card : ℝ) ≤
          ∑ d ∈ levelDivisors z (2 * r + 1),
            (((Ioc a b).filter fun n => d ∣ n).card : ℝ) := by
  have h := sum_bonferroni_error (Ioc a b) (omegaSmall z) r
  have hid : (∑ n ∈ Ioc a b, ((omegaSmall z n).choose (2 * r + 1) : ℝ)) =
      ∑ d ∈ levelDivisors z (2 * r + 1),
        (((Ioc a b).filter fun n => d ∣ n).card : ℝ) := by
    exact_mod_cast sum_choose_omegaSmall_eq z a b (2 * r + 1)
  rwa [hid] at h

end GaloisForLFunctions.BezoutValuationIncidence.Sieve

#print axioms GaloisForLFunctions.BezoutValuationIncidence.Sieve.bonferroni_one_bounds
#print axioms GaloisForLFunctions.BezoutValuationIncidence.Sieve.sum_bonferroni_error
#print axioms GaloisForLFunctions.BezoutValuationIncidence.Sieve.omegaSmall_bonferroni_error
