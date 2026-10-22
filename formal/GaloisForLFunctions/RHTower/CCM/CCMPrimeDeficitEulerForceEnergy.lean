import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitEulerForceOrthogonality
import GaloisForLFunctions.RHTower.Sieve.CriticalDivisorAffineMeanSquare

/-!
# Uniform critical coefficient energy of the complete prime force

The quadratic rough coefficient is at most the divisor function. The
logarithmic derivation of zeta squared gives a factor one half in its
prime force. The corpus's fourth harmonic divisor moment then bounds
the complete force energy by an explicit sixth-degree logarithmic scale,
uniformly in the Euler modulus. This is a coefficient-energy estimate;
the signed time-domain reconstruction still needs cancellation.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

private theorem real_zeta_sq_apply (n : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 2) n = (n.divisors.card : ℝ) := by
  rw [pow_two, ArithmeticFunction.coe_mul_zeta_apply]
  calc
    (∑ d ∈ n.divisors, (ArithmeticFunction.zeta : ArithmeticFunction ℝ) d) =
        ∑ _d ∈ n.divisors, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply_ne (Nat.pos_of_mem_divisors hd).ne', Nat.cast_one]
    _ = _ := by simp

theorem ccmEulerRenewalKernel_le_divisor_count (P n : ℕ) :
    ccmEulerRenewalKernel P n ≤ (n.divisors.card : ℝ) := by
  rw [ccmEulerRenewalKernel, pow_two, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d e => ccmEulerRough P d * ccmEulerRough P e)]
  calc
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := Finset.sum_le_sum fun d _ =>
      mul_le_one₀ (ccmEulerRough_le_one _ _) (ccmEulerRough_nonneg _ _)
        (ccmEulerRough_le_one _ _)
    _ = _ := by simp

theorem ccmEulerRenewal_fullForce_nonneg (P n : ℕ) :
    0 ≤ (ccmEulerRenewalKernel P * ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg fun de _ => mul_nonneg (ccmEulerRenewalKernel_nonneg P de.1)
    ArithmeticFunction.vonMangoldt_nonneg

/-- A modulus-independent bound for the complete prime force. -/
theorem ccmEulerRenewal_fullForce_le_divisor_log (P n : ℕ) :
    (ccmEulerRenewalKernel P * ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n ≤
      (n.divisors.card : ℝ) * Real.log n / 2 := by
  have hm : (ccmEulerRenewalKernel P * ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n ≤
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 2 * ArithmeticFunction.vonMangoldt) n := by
    rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
    apply Finset.sum_le_sum
    intro de _
    apply mul_le_mul_of_nonneg_right _ ArithmeticFunction.vonMangoldt_nonneg
    rw [real_zeta_sq_apply]
    exact ccmEulerRenewalKernel_le_divisor_count P de.1
  have hd : logDerivation ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 2) =
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 2 * ArithmeticFunction.vonMangoldt +
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 2 * ArithmeticFunction.vonMangoldt := by
    rw [pow_two, logDerivation_mul, logDerivation_zeta, ← ArithmeticFunction.zeta_mul_vonMangoldt]
    ring
  have hv := congrArg (fun f : ArithmeticFunction ℝ => f n) hd
  rw [logDerivation_apply, real_zeta_sq_apply, ArithmeticFunction.add_apply] at hv
  linarith only [hm, hv]

/-- The actual complete force has only logarithmic critical coefficient energy. -/
theorem ccmEulerRenewal_fullForce_critical_energy_le (P N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
      (ccmEulerRenewalKernel P * ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n ^ 2 / n) ≤
      (Real.log N) ^ 2 / 4 * (1 + Real.log N) ^ 4 := by
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (Real.log N) ^ 2 / 4 * ((n.divisors.card : ℝ) ^ 2 / n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hlog : Real.log n ≤ Real.log N := Real.log_le_log hnpos
        (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
      have hF0 := ccmEulerRenewal_fullForce_nonneg P n
      have hF := ccmEulerRenewal_fullForce_le_divisor_log P n
      calc
        _ ≤ ((n.divisors.card : ℝ) * Real.log N / 2) ^ 2 / n := by
          gcongr
          exact hF.trans (by gcongr)
        _ = _ := by ring
    _ = (Real.log N) ^ 2 / 4 *
        ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 / n := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Sieve.sum_card_divisors_sq_div_le_polylog N hN)
      (by positivity)

/-- The exact disjoint-channel energy obeys the same uniform estimate. -/
theorem ccmEulerRenewal_split_critical_energy_le (P N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
      (ccmEulerRenewalKernel P * ccmEulerSurvivingPrime P : ArithmeticFunction ℝ) n ^ 2 / n) +
    (∑ n ∈ Finset.Icc 1 N,
      (ccmEulerRenewalKernel P * ccmEulerDeletedPrime P : ArithmeticFunction ℝ) n ^ 2 / n) ≤
      (Real.log N) ^ 2 / 4 * (1 + Real.log N) ^ 4 := by
  have he :
      (∑ n ∈ Finset.Icc 1 N,
        (ccmEulerRenewalKernel P * ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n ^ 2 / n) =
      (∑ n ∈ Finset.Icc 1 N,
        (ccmEulerRenewalKernel P * ccmEulerSurvivingPrime P : ArithmeticFunction ℝ) n ^ 2 / n) +
      ∑ n ∈ Finset.Icc 1 N,
        (ccmEulerRenewalKernel P * ccmEulerDeletedPrime P : ArithmeticFunction ℝ) n ^ 2 / n := by
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using
      ccmEulerRenewal_prime_energy_split P (Finset.Icc 1 N) (fun n => 1 / (n : ℝ))
  rw [← he]
  exact ccmEulerRenewal_fullForce_critical_energy_le P N hN

end RHTower
