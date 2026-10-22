import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitEulerDeletedEnergy
import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitEulerForceEnergy
import GaloisForLFunctions.RHTower.VonMangoldtLogHarmonicSummatory

/-!
# Logarithmic cost of the factorial Euler cutoff

The tower budget of the modulus `m!` is controlled by primes at most `m`.
The existing logarithmic von Mangoldt moment bounds it quadratically in
`log m`, rather than in `log (m!)`. All horizons and cutoff values are
included, with no unproved cancellation premise.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

/-- The rough renewal kernel has the fourth harmonic divisor moment bound. -/
theorem ccmEulerRenewalKernel_critical_energy_le (P N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ccmEulerRenewalKernel P n ^ 2 / n) ≤
      (1 + Real.log N) ^ 4 := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  apply le_trans (Finset.sum_le_sum fun n _ => ?_)
    (Sieve.sum_card_divisors_sq_div_le_polylog N (Nat.one_le_iff_ne_zero.mpr hN))
  have hb0 := ccmEulerRenewalKernel_nonneg P n
  gcongr
  exact ccmEulerRenewalKernel_le_divisor_count P n

/-- Deleted-force critical energy for every positive Euler modulus. -/
theorem ccmEulerRenewal_deletedForce_critical_energy_le (P N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      (ccmEulerRenewalKernel (P + 1) * ccmEulerDeletedPrime (P + 1) : ArithmeticFunction ℝ) n ^ 2 / n) ≤
      ccmEulerDeletedEnergyBudget (P + 1) * (1 + Real.log N) ^ 4 := by
  exact (ccmEulerRenewal_deletedForce_energy_le_budget P N).trans
    (mul_le_mul_of_nonneg_left (ccmEulerRenewalKernel_critical_energy_le (P + 1) N)
      (ccmEulerDeletedEnergyBudget_nonneg (P + 1)))

/-- The factorial budget is paid by a logarithmic von Mangoldt moment. -/
theorem ccmEulerDeletedEnergyBudget_factorial_le_moment (m : ℕ) :
    ccmEulerDeletedEnergyBudget m.factorial ≤
      2 * ∑ n ∈ Finset.Icc 1 m, ArithmeticFunction.vonMangoldt n * Real.log n / n := by
  unfold ccmEulerDeletedEnergyBudget
  calc
    _ ≤ ∑ p ∈ m.factorial.primeFactors,
        2 * (ArithmeticFunction.vonMangoldt p * Real.log p / p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpprime := Nat.prime_of_mem_primeFactors hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpprime.two_le
      have hp0 : (0 : ℝ) < p := by linarith
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      rw [ArithmeticFunction.vonMangoldt_apply_prime hpprime]
      have hrecip : (1 : ℝ) / ((p : ℝ) - 1) ≤ 2 / p := by
        rw [div_le_div_iff₀ hp1 hp0]
        linarith
      calc
        _ = (Real.log p) ^ 2 * (1 / ((p : ℝ) - 1)) := by ring
        _ ≤ (Real.log p) ^ 2 * (2 / p) :=
          mul_le_mul_of_nonneg_left hrecip (sq_nonneg _)
        _ = _ := by ring
    _ ≤ ∑ n ∈ Finset.Icc 1 m,
        2 * (ArithmeticFunction.vonMangoldt n * Real.log n / n) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hpprime := Nat.prime_of_mem_primeFactors hp
        exact Finset.mem_Icc.mpr ⟨hpprime.one_lt.le,
          hpprime.dvd_factorial.mp (Nat.dvd_of_mem_primeFactors hp)⟩
      · intro n _ _
        exact mul_nonneg (by positivity) (div_nonneg
          (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg n))
          (Nat.cast_nonneg n))
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The cost depends quadratically on the logarithm of the cutoff. -/
theorem ccmEulerDeletedEnergyBudget_factorial_le (m : ℕ) :
    ccmEulerDeletedEnergyBudget m.factorial ≤
      (Real.log m) ^ 2 + 30 * Real.log m + 2 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [ccmEulerDeletedEnergyBudget]
  have hmoment := (abs_le.mp
    (abs_sum_vonMangoldt_log_div_sub_le m (Nat.one_le_iff_ne_zero.mpr hm))).2
  have hbudget := ccmEulerDeletedEnergyBudget_factorial_le_moment m
  linarith only [hmoment, hbudget]

/-- Explicit deleted-force energy bound for the actual factorial cutoffs. -/
theorem ccmEulerRenewal_deletedForce_factorial_critical_energy_le (m N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      (ccmEulerRenewalKernel m.factorial * ccmEulerDeletedPrime m.factorial : ArithmeticFunction ℝ) n ^ 2 / n) ≤
      ((Real.log m) ^ 2 + 30 * Real.log m + 2) * (1 + Real.log N) ^ 4 := by
  have hfac : m.factorial - 1 + 1 = m.factorial :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m))
  have hbase := ccmEulerRenewal_deletedForce_critical_energy_le (m.factorial - 1) N
  rw [hfac] at hbase
  exact hbase.trans (mul_le_mul_of_nonneg_right
    (ccmEulerDeletedEnergyBudget_factorial_le m) (by positivity))

end RHTower
