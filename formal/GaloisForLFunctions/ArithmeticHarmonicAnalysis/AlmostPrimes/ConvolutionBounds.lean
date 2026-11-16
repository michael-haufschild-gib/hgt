import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-!
# Unconditional bounds for almost-prime coefficients

The coefficients of `(-ζ'/ζ)^k` in arXiv:2611.05000 are Dirichlet powers
of von Mangoldt. Positivity and the divisor identity `Σ_{d|n} Λ(d) = log n`
give a bound at every convolution order. Nonzero coefficients have at most
that many distinct prime factors.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlmostPrimes

theorem convolution_nonneg (k n : ℕ) : 0 ≤ (Λ ^ k) n := by
  induction k generalizing n with
  | zero => simp only [pow_zero, ArithmeticFunction.one_apply]; split_ifs <;> positivity
  | succ k ih =>
    rw [pow_succ', ArithmeticFunction.mul_apply]
    exact sum_nonneg fun d _ => mul_nonneg vonMangoldt_nonneg (ih d.2)

/-- A logarithmic envelope valid at all orders and all integer arguments. -/
theorem convolution_le_log_pow (k n : ℕ) : (Λ ^ k) n ≤ Real.log n ^ k := by
  induction k generalizing n with
  | zero => simp only [pow_zero, ArithmeticFunction.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ', ArithmeticFunction.mul_apply]
    calc
      ∑ d ∈ n.divisorsAntidiagonal, Λ d.1 * (Λ ^ k) d.2 ≤
          ∑ d ∈ n.divisorsAntidiagonal, Λ d.1 * Real.log n ^ k := by
        apply sum_le_sum
        intro d hd
        obtain ⟨hdn, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hd
        have hd2 : d.2 ≠ 0 := by intro h; simp [h] at hdn; exact hn hdn.symm
        have hle : d.2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
          ⟨d.1, by simpa only [mul_comm] using hdn.symm⟩
        have hlog := Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hd2)
          (show (d.2 : ℝ) ≤ n by exact_mod_cast hle)
        exact mul_le_mul_of_nonneg_left
          ((ih d.2).trans (pow_le_pow_left₀ (Real.log_natCast_nonneg _) hlog k))
          vonMangoldt_nonneg
      _ = Real.log n ^ (k + 1) := by
        rw [Nat.sum_divisorsAntidiagonal (fun d _ => Λ d * Real.log n ^ k),
          ← sum_mul, vonMangoldt_sum, pow_succ]
        ring

/-- Each nonzero convolution factor contributes at most one new prime. -/
theorem convolution_eq_zero_of_card_lt (k n : ℕ) :
    k < n.primeFactors.card → (Λ ^ k) n = 0 := by
  induction k generalizing n with
  | zero =>
    intro hn
    have hn1 : n ≠ 1 := by intro h; simp [h] at hn
    simp [hn1]
  | succ k ih =>
    intro hn
    rw [pow_succ', ArithmeticFunction.mul_apply]
    apply sum_eq_zero
    intro d hd
    by_cases hfirst : Λ d.1 = 0
    · rw [hfirst, zero_mul]
    have hprime := vonMangoldt_ne_zero_iff.mp hfirst
    obtain ⟨hdn, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hd
    have hd1 : d.1 ≠ 0 := by intro h; simp [h] at hdn; exact hn0 hdn.symm
    have hd2 : d.2 ≠ 0 := by intro h; simp [h] at hdn; exact hn0 hdn.symm
    have hcard : n.primeFactors.card ≤ 1 + d.2.primeFactors.card := by
      rw [← hdn, Nat.primeFactors_mul hd1 hd2]
      simpa only [isPrimePow_iff_card_primeFactors_eq_one.mp hprime] using
        card_union_le d.1.primeFactors d.2.primeFactors
    rw [ih d.2 (by omega), mul_zero]

/-- The squared coefficients needed by mean-square estimates retain the same envelope. -/
theorem convolution_sq_le_log_pow (k n : ℕ) :
    ((Λ ^ k) n) ^ 2 ≤ Real.log n ^ (2 * k) := by
  calc ((Λ ^ k) n) ^ 2 ≤ (Real.log n ^ k) ^ 2 :=
      pow_le_pow_left₀ (convolution_nonneg k n) (convolution_le_log_pow k n) 2
    _ = _ := by rw [← pow_mul, Nat.mul_comm k 2]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlmostPrimes
