import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitEulerPrimeSplit

/-!
# Half of the logarithmic moment pays for surviving-prime force

The logarithmic product rule gives an exact balance for the quadratic
renewal coefficient. Its surviving-prime force is at most half of its
logarithmic moment; the difference is the lower-order rough prime force.
Deleted-prime force remains in the actual signed work identity.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

theorem logDerivation_ccmEulerRenewalKernel (P : ℕ) :
    logDerivation (ccmEulerRenewalKernel P) =
      (ccmEulerRenewalKernel P + ccmEulerRough P) * ccmEulerSurvivingPrime P +
        (ccmEulerRenewalKernel P + ccmEulerRough P) * ccmEulerSurvivingPrime P := by
  rw [ccmEulerRenewalKernel, pow_two, logDerivation_mul, logDerivation_ccmEulerRough]
  ring

/-- Exact coefficient conservation with the literal half-logarithmic normalization. -/
theorem ccmEulerRenewal_surviving_force_balance (P n : ℕ) :
    ccmEulerRenewalKernel P n * Real.log n =
      2 * (ccmEulerRenewalKernel P * ccmEulerSurvivingPrime P : ArithmeticFunction ℝ) n +
      2 * (ccmEulerRough P * ccmEulerSurvivingPrime P : ArithmeticFunction ℝ) n := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (logDerivation_ccmEulerRenewalKernel P)
  rw [logDerivation_apply, add_mul, ArithmeticFunction.add_apply,
    ArithmeticFunction.add_apply] at h
  linarith only [h]

theorem ccmEulerRough_survivingForce_nonneg (P n : ℕ) :
    0 ≤ (ccmEulerRough P * ccmEulerSurvivingPrime P : ArithmeticFunction ℝ) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg fun de _ => mul_nonneg (ccmEulerRough_nonneg P de.1)
    (ccmEulerSurvivingPrime_nonneg P de.2)

theorem ccmEulerRenewal_survivingForce_le_half_log (P n : ℕ) :
    (ccmEulerRenewalKernel P * ccmEulerSurvivingPrime P : ArithmeticFunction ℝ) n ≤
      ccmEulerRenewalKernel P n * Real.log n / 2 := by
  linarith only [ccmEulerRenewal_surviving_force_balance P n,
    ccmEulerRough_survivingForce_nonneg P n]

def ccmEulerSurvivingWork (P : ℕ) (T : ℝ) : ℝ :=
  logarithmicWeightedDilation
    (ccmEulerRenewalKernel P * ccmEulerSurvivingPrime P : ArithmeticFunction ℝ) logarithmicLinearRamp T

def ccmEulerDeletedWork (P : ℕ) (T : ℝ) : ℝ :=
  logarithmicWeightedDilation
    (ccmEulerRenewalKernel P * ccmEulerDeletedPrime P : ArithmeticFunction ℝ) logarithmicLinearRamp T

def ccmEulerLogMomentWork (P : ℕ) (T : ℝ) : ℝ :=
  logarithmicWeightedDilation (logDerivation (ccmEulerRenewalKernel P)) logarithmicLinearRamp T

def ccmEulerLowerPrimeWork (P : ℕ) (T : ℝ) : ℝ :=
  logarithmicWeightedDilation
    (ccmEulerRough P * ccmEulerSurvivingPrime P : ArithmeticFunction ℝ) logarithmicLinearRamp T

theorem ccmPrimeDeficitEulerPrimeWork_split (P : ℕ) (T : ℝ) :
    ccmPrimeDeficitEulerPrimeWork P T = ccmEulerSurvivingWork P T + ccmEulerDeletedWork P T := by
  rw [ccmPrimeDeficitEulerPrimeWork, logarithmicWeightedDilation_arithmetic_mul]
  have hc : (ccmEulerRough P * ArithmeticFunction.vonMangoldt) * ccmEulerRough P =
      ccmEulerRenewalKernel P * ccmEulerSurvivingPrime P +
        ccmEulerRenewalKernel P * ccmEulerDeletedPrime P := by
    rw [← ccmEuler_prime_split P, ccmEulerRenewalKernel]
    ring
  rw [hc]
  exact logarithmicWeightedDilation_add_coeff _ _ _ _

theorem ccmEulerLogMomentWork_balance (P : ℕ) (T : ℝ) :
    ccmEulerLogMomentWork P T = 2 * ccmEulerSurvivingWork P T + 2 * ccmEulerLowerPrimeWork P T := by
  unfold ccmEulerLogMomentWork ccmEulerSurvivingWork ccmEulerLowerPrimeWork logarithmicWeightedDilation
  simp_rw [logDerivation_apply, ccmEulerRenewal_surviving_force_balance,
    add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem ccmEulerLowerPrimeWork_nonneg (P : ℕ) (T : ℝ) : 0 ≤ ccmEulerLowerPrimeWork P T := by
  unfold ccmEulerLowerPrimeWork logarithmicWeightedDilation
  exact Finset.sum_nonneg fun n _ => mul_nonneg (ccmEulerRough_survivingForce_nonneg P n)
    (le_max_right _ _)

theorem ccmEulerSurvivingWork_le_half_logMoment (P : ℕ) (T : ℝ) :
    ccmEulerSurvivingWork P T ≤ ccmEulerLogMomentWork P T / 2 := by
  linarith only [ccmEulerLogMomentWork_balance P T, ccmEulerLowerPrimeWork_nonneg P T]

/-- The complete signed error, preserving both the lower-order correction
and the force from primes removed by the Euler product. -/
theorem ccmLogChebyshevDeficitPrimitive_sub_eulerAction_halfLog_balance
    (P : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitEulerAction P T =
      ccmPrimeDeficitEulerExponentialWork P T - ccmEulerLogMomentWork P T / 2 +
        ccmEulerLowerPrimeWork P T - ccmEulerDeletedWork P T := by
  rw [ccmLogChebyshevDeficitPrimitive_sub_eulerAction_eq_work_difference P hT,
    ccmPrimeDeficitEulerPrimeWork_split]
  linarith only [ccmEulerLogMomentWork_balance P T]

end RHTower
