import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitResidualPairing
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# The residual force is the existing sieve defect driven by primes

The residual divisor coefficient is exactly `Sieve.moebiusZetaDefect`.
Its logarithmic partner is its Dirichlet convolution with von Mangoldt.
Consequently the prime force starts no earlier than `2(m+1)`, while the
residual coefficient itself starts at `m+1`.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

private def arithmeticMobiusTail (m : ℕ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ) - Sieve.truncatedMoebius m

private theorem arithmeticMobiusTail_apply (m n : ℕ) :
    arithmeticMobiusTail m n = logarithmicLongTail m moebiusCoeff n := by
  change (ArithmeticFunction.moebius n : ℝ) -
    (if n ≤ m then (ArithmeticFunction.moebius n : ℝ) else 0) =
      if m < n then (ArithmeticFunction.moebius n : ℝ) else 0
  by_cases hn : n ≤ m
  · simp [hn, not_lt.mpr hn]
  · simp [hn, Nat.lt_of_not_ge hn]

private theorem arithmeticMobiusTail_mul_zeta (m : ℕ) :
    arithmeticMobiusTail m * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
      Sieve.moebiusZetaDefect m := by
  unfold arithmeticMobiusTail Sieve.moebiusZetaDefect
  rw [sub_mul, ArithmeticFunction.coe_moebius_mul_coe_zeta]

/-- The reflection coefficient reuses the corpus's established sieve defect. -/
theorem ccmPrimeDeficitResidualCoeff_eq_sieveDefect (m n : ℕ) :
    ccmPrimeDeficitResidualCoeff m n = Sieve.moebiusZetaDefect m n := by
  rw [ccmPrimeDeficitResidualCoeff, logarithmicDivisorTransform]
  simp_rw [← arithmeticMobiusTail_apply m]
  rw [← ArithmeticFunction.coe_mul_zeta_apply, arithmeticMobiusTail_mul_zeta]

/-- Exact prime forcing: the second residual is the first residual
convolved with the literal von Mangoldt arithmetic function. -/
theorem ccmPrimeDeficitResidualLogCoeff_eq_sieveDefect_mul_vonMangoldt (m n : ℕ) :
    ccmPrimeDeficitResidualLogCoeff m n =
      (Sieve.moebiusZetaDefect m * ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n := by
  have hl : ccmPrimeDeficitResidualLogCoeff m n =
      (arithmeticMobiusTail m * ArithmeticFunction.log : ArithmeticFunction ℝ) n := by
    rw [ccmPrimeDeficitResidualLogCoeff, logarithmicLogDivisorTransform,
      ArithmeticFunction.mul_apply]
    simp_rw [← arithmeticMobiusTail_apply m, ArithmeticFunction.log_apply]
    exact (Nat.sum_divisorsAntidiagonal (fun d e => arithmeticMobiusTail m d * Real.log e)).symm
  rw [hl, ← ArithmeticFunction.zeta_mul_vonMangoldt, ← mul_assoc, arithmeticMobiusTail_mul_zeta]

theorem ccmPrimeDeficitResidualLogCoeff_eq_prime_divisor_sum (m n : ℕ) :
    ccmPrimeDeficitResidualLogCoeff m n =
      ∑ d ∈ n.divisors, ccmPrimeDeficitResidualCoeff m d *
        ArithmeticFunction.vonMangoldt (n / d) := by
  rw [ccmPrimeDeficitResidualLogCoeff_eq_sieveDefect_mul_vonMangoldt,
    ArithmeticFunction.mul_apply]
  simp_rw [ccmPrimeDeficitResidualCoeff_eq_sieveDefect]
  exact Nat.sum_divisorsAntidiagonal
    (fun d e => Sieve.moebiusZetaDefect m d * ArithmeticFunction.vonMangoldt e)

theorem ccmPrimeDeficitResidualCoeff_of_le {m n : ℕ} (hn : n ≤ m) :
    ccmPrimeDeficitResidualCoeff m n = 0 := by
  rw [ccmPrimeDeficitResidualCoeff_eq_sieveDefect]
  exact Sieve.moebiusZetaDefect_vanishesBelow m n (by omega)

/-- The prime force has twice the residual's entry threshold. -/
theorem ccmPrimeDeficitResidualLogCoeff_of_lt_twice {m n : ℕ} (hn : n < 2 * (m + 1)) :
    ccmPrimeDeficitResidualLogCoeff m n = 0 := by
  have hv : Sieve.VanishesBelow ArithmeticFunction.vonMangoldt 2 := by
    intro j hj
    by_cases hj0 : j = 0
    · simp [hj0]
    · have hj1 : j = 1 := by omega
      simp [hj1]
  rw [ccmPrimeDeficitResidualLogCoeff_eq_sieveDefect_mul_vonMangoldt]
  exact Sieve.vanishesBelow_mul (Sieve.moebiusZetaDefect_vanishesBelow m) hv n (by omega)

private theorem moebiusZetaDefect_zero : Sieve.moebiusZetaDefect 0 = 1 := by
  have htr : Sieve.truncatedMoebius 0 = 0 := by
    ext n
    by_cases hn : n = 0
    · simp [hn]
    · simp [Sieve.truncatedMoebius_apply, hn]
  simp [Sieve.moebiusZetaDefect, htr]

theorem ccmPrimeDeficitResidualCoeff_zero_cutoff (n : ℕ) :
    ccmPrimeDeficitResidualCoeff 0 n = if n = 1 then 1 else 0 := by
  rw [ccmPrimeDeficitResidualCoeff_eq_sieveDefect, moebiusZetaDefect_zero]
  rfl

theorem ccmPrimeDeficitResidualLogCoeff_zero_cutoff (n : ℕ) :
    ccmPrimeDeficitResidualLogCoeff 0 n = ArithmeticFunction.vonMangoldt n := by
  rw [ccmPrimeDeficitResidualLogCoeff_eq_sieveDefect_mul_vonMangoldt,
    moebiusZetaDefect_zero, one_mul]

end RHTower
