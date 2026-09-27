import GaloisForLFunctions.RHTower.CCMPrimeDeficitEulerResolvent
import GaloisForLFunctions.RHTower.LocalizedHalfDensityCurvature

/-!
# The literal prime split of Euler completion

The coprime indicator is completely multiplicative. Its logarithmic
derivation is its convolution with von Mangoldt restricted to the same
coprime support. The complementary prime force is retained explicitly.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

def ccmEulerCoprime (P : ℕ) : ArithmeticFunction ℝ := 1 + ccmEulerRough P

def ccmEulerSurvivingPrime (P : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul (ccmEulerCoprime P) ArithmeticFunction.vonMangoldt

def ccmEulerDeletedPrime (P : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.vonMangoldt - ccmEulerSurvivingPrime P

theorem ccmEulerCoprime_apply (P n : ℕ) :
    ccmEulerCoprime P n = if n = 0 then 0 else if n.Coprime P then 1 else 0 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  change (if n = 1 then (1 : ℝ) else 0) +
    (if 1 < n ∧ n.Coprime P then 1 else 0) = _
  by_cases hn1 : n = 1
  · simp [hn1]
  · have hn2 : 1 < n := by omega
    simp [hn0, hn1, hn2]

theorem ccmEulerCoprime_mul (P a b : ℕ) :
    ccmEulerCoprime P (a * b) = ccmEulerCoprime P a * ccmEulerCoprime P b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  simp only [ccmEulerCoprime_apply, if_neg ha, if_neg hb, if_neg (mul_ne_zero ha hb),
    Nat.coprime_mul_iff_left]
  split_ifs <;> simp_all

theorem ccmEulerSurvivingPrime_apply (P n : ℕ) :
    ccmEulerSurvivingPrime P n =
      if n.Coprime P then ArithmeticFunction.vonMangoldt n else 0 := by
  rw [ccmEulerSurvivingPrime, ArithmeticFunction.pmul_apply, ccmEulerCoprime_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [if_neg hn]
    split <;> simp

theorem ccmEulerDeletedPrime_apply (P n : ℕ) :
    ccmEulerDeletedPrime P n =
      if n.Coprime P then 0 else ArithmeticFunction.vonMangoldt n := by
  simp only [ccmEulerDeletedPrime, sub_eq_add_neg, ArithmeticFunction.add_apply,
    ArithmeticFunction.neg_apply, ccmEulerSurvivingPrime_apply]
  split <;> simp

theorem ccmEulerSurvivingPrime_nonneg (P n : ℕ) : 0 ≤ ccmEulerSurvivingPrime P n := by
  rw [ccmEulerSurvivingPrime_apply]
  split
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

theorem ccmEulerDeletedPrime_nonneg (P n : ℕ) : 0 ≤ ccmEulerDeletedPrime P n := by
  rw [ccmEulerDeletedPrime_apply]
  split
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

theorem ccmEuler_prime_split (P : ℕ) :
    ccmEulerSurvivingPrime P + ccmEulerDeletedPrime P = ArithmeticFunction.vonMangoldt := by
  unfold ccmEulerDeletedPrime
  abel

/-- The logarithmic derivative uses precisely the primes surviving Euler deletion. -/
theorem logDerivation_ccmEulerCoprime (P : ℕ) :
    logDerivation (ccmEulerCoprime P) = ccmEulerCoprime P * ccmEulerSurvivingPrime P := by
  ext n
  rw [logDerivation_apply, ArithmeticFunction.mul_apply]
  calc
    ccmEulerCoprime P n * Real.log n =
        ccmEulerCoprime P n * ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d := by
      rw [ArithmeticFunction.vonMangoldt_sum]
    _ = ∑ de ∈ n.divisorsAntidiagonal,
        ccmEulerCoprime P n * ArithmeticFunction.vonMangoldt de.2 := by
      rw [Nat.sum_divisorsAntidiagonal' (fun _ e =>
        ccmEulerCoprime P n * ArithmeticFunction.vonMangoldt e), Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro de hde
      rw [← (Nat.mem_divisorsAntidiagonal.mp hde).1, ccmEulerCoprime_mul,
        ccmEulerSurvivingPrime, ArithmeticFunction.pmul_apply]
      ring

theorem logDerivation_ccmEulerRough (P : ℕ) :
    logDerivation (ccmEulerRough P) =
      (1 + ccmEulerRough P) * ccmEulerSurvivingPrime P := by
  rw [← ccmEulerCoprime, ← logDerivation_ccmEulerCoprime]
  ext n
  rw [logDerivation_apply, logDerivation_apply, ccmEulerCoprime,
    ArithmeticFunction.add_apply, add_mul]
  have hz : (1 : ArithmeticFunction ℝ) n * Real.log n = 0 := by
    rcases eq_or_ne n 1 with rfl | hn
    · simp
    · rw [ArithmeticFunction.one_apply_ne hn, zero_mul]
  rw [hz, zero_add]

/-- The surviving force is a logarithmic moment with its prime atom removed. -/
theorem ccmEulerRough_mul_survivingPrime (P n : ℕ) :
    (ccmEulerRough P * ccmEulerSurvivingPrime P : ArithmeticFunction ℝ) n =
      ccmEulerRough P n * Real.log n - ccmEulerSurvivingPrime P n := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (logDerivation_ccmEulerRough P)
  rw [logDerivation_apply, add_mul, one_mul, ArithmeticFunction.add_apply] at h
  linarith only [h]

end RHTower
