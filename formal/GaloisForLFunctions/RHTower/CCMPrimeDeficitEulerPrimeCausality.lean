import GaloisForLFunctions.RHTower.CCMPrimeDeficitEulerForceBalance

/-!
# Cubic delay before surviving-prime force can enter

For the factorial completion at `m`, each nontrivial rough factor and
each surviving prime power exceeds `m`. Two rough factors and one
surviving prime therefore have no interaction below `(m+1)^3`.
The earlier forcing is exactly the deleted-prime contribution.
-/

noncomputable section

namespace RHTower

theorem ccmEulerSurvivingPrime_factorial_of_le {m n : ℕ} (hn : n ≤ m) :
    ccmEulerSurvivingPrime m.factorial n = 0 := by
  rw [ccmEulerSurvivingPrime, ArithmeticFunction.pmul_apply, ccmEulerCoprime,
    ArithmeticFunction.add_apply, ccmEulerRough_factorial_of_le hn, add_zero]
  rcases eq_or_ne n 1 with rfl | hn1
  · simp
  · rw [ArithmeticFunction.one_apply_ne hn1, zero_mul]

theorem ccmEulerRough_factorial_vanishesBelow (m : ℕ) :
    Sieve.VanishesBelow (ccmEulerRough m.factorial) (m + 1) :=
  fun _ hn => ccmEulerRough_factorial_of_le (by omega)

theorem ccmEulerSurvivingPrime_factorial_vanishesBelow (m : ℕ) :
    Sieve.VanishesBelow (ccmEulerSurvivingPrime m.factorial) (m + 1) :=
  fun _ hn => ccmEulerSurvivingPrime_factorial_of_le (by omega)

theorem ccmEulerRenewal_factorial_vanishesBelow (m : ℕ) :
    Sieve.VanishesBelow (ccmEulerRenewalKernel m.factorial) ((m + 1) ^ 2) :=
  Sieve.vanishesBelow_pow (ccmEulerRough_factorial_vanishesBelow m)

/-- Surviving-prime force requires three factors beyond the retained cutoff. -/
theorem ccmEulerRenewal_survivingForce_factorial_vanishesBelow (m : ℕ) :
    Sieve.VanishesBelow
      (ccmEulerRenewalKernel m.factorial * ccmEulerSurvivingPrime m.factorial) ((m + 1) ^ 3) := by
  simpa only [pow_succ] using Sieve.vanishesBelow_mul
    (ccmEulerRenewal_factorial_vanishesBelow m) (ccmEulerSurvivingPrime_factorial_vanishesBelow m)

theorem ccmEulerSurvivingWork_factorial_eq_zero_before_cubic (m : ℕ) {T : ℝ}
    (hT : ⌊Real.exp T⌋₊ < (m + 1) ^ 3) :
    ccmEulerSurvivingWork m.factorial T = 0 := by
  unfold ccmEulerSurvivingWork logarithmicWeightedDilation
  apply Finset.sum_eq_zero
  intro n hn
  rw [ccmEulerRenewal_survivingForce_factorial_vanishesBelow m n
    ((Finset.mem_Icc.mp hn).2.trans_lt hT), zero_mul]

theorem ccmPrimeDeficitEulerPrimeWork_factorial_eq_deleted_before_cubic (m : ℕ) {T : ℝ}
    (hT : ⌊Real.exp T⌋₊ < (m + 1) ^ 3) :
    ccmPrimeDeficitEulerPrimeWork m.factorial T = ccmEulerDeletedWork m.factorial T := by
  rw [ccmPrimeDeficitEulerPrimeWork_split,
    ccmEulerSurvivingWork_factorial_eq_zero_before_cubic m hT, zero_add]

/-- The half-logarithmic moment and lower-order prime correction cancel
exactly throughout the cubic causal window. -/
theorem ccmEuler_halfLog_cancellation_before_cubic (m : ℕ) {T : ℝ}
    (hT : ⌊Real.exp T⌋₊ < (m + 1) ^ 3) :
    ccmEulerLogMomentWork m.factorial T / 2 = ccmEulerLowerPrimeWork m.factorial T := by
  rw [ccmEulerLogMomentWork_balance, ccmEulerSurvivingWork_factorial_eq_zero_before_cubic m hT]
  ring

theorem ccmLogChebyshevDeficitPrimitive_sub_eulerAction_eq_deleted_balance_before_cubic
    (m : ℕ) {T : ℝ} (h0 : 0 ≤ T) (hT : ⌊Real.exp T⌋₊ < (m + 1) ^ 3) :
    ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitEulerAction m.factorial T =
      ccmPrimeDeficitEulerExponentialWork m.factorial T - ccmEulerDeletedWork m.factorial T := by
  rw [ccmLogChebyshevDeficitPrimitive_sub_eulerAction_eq_work_difference m.factorial h0,
    ccmPrimeDeficitEulerPrimeWork_factorial_eq_deleted_before_cubic m hT]

end RHTower
