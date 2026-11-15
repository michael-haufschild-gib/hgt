import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusTracePolynomials

/-!
# Parity of geometric-sum Kummer exponents

Modulo `q+1`, the geometric sum `1+q+⋯+q^(r-1)` is zero for even `r`
and one for odd `r`. The resulting gcd formulas determine ramification
and regular-differential dimensions in degree-`q+1` Kummer extensions.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Finset

/-- Prepending the constant term gives the geometric-sum recurrence. -/
theorem kummerExponent_succ (q r : ℕ) :
    kummerExponent q (r + 1) = q * kummerExponent q r + 1 := by
  unfold kummerExponent
  rw [Finset.sum_range_succ']
  simp only [pow_succ', pow_zero, Finset.mul_sum]

/-- An even number of terms pairs into multiples of `q+1`. -/
theorem kummerExponent_even_dvd (q n : ℕ) : q + 1 ∣ kummerExponent q (2 * n) := by
  induction n with
  | zero => simp [kummerExponent]
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨q ^ 2 * k + 1, ?_⟩
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega,
      kummerExponent_succ, kummerExponent_succ, hk]
    ring

theorem kummerExponent_even_mod (q n : ℕ) :
    kummerExponent q (2 * n) % (q + 1) = 0 :=
  Nat.mod_eq_zero_of_dvd (kummerExponent_even_dvd q n)

theorem kummerExponent_odd_mod (q n : ℕ) :
    kummerExponent q (2 * n + 1) % (q + 1) = 1 % (q + 1) := by
  rw [kummerExponent_succ, Nat.add_mod, Nat.mul_mod, kummerExponent_even_mod]
  simp only [mul_zero, Nat.zero_mod, zero_add, Nat.mod_mod]

theorem kummerExponent_even_gcd (q n : ℕ) :
    Nat.gcd (q + 1) (kummerExponent q (2 * n)) = q + 1 :=
  Nat.gcd_eq_left (kummerExponent_even_dvd q n)

theorem kummerExponent_odd_gcd (q n : ℕ) :
    Nat.gcd (q + 1) (kummerExponent q (2 * n + 1)) = 1 := by
  rw [Nat.gcd_rec (q + 1) (kummerExponent q (2 * n + 1)), kummerExponent_odd_mod,
    ← Nat.gcd_rec (q + 1) 1, Nat.gcd_one_right]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
