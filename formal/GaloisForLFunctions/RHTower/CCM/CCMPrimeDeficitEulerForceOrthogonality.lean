import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitEulerForceBalance

/-!
# Disjoint arithmetic supports of the two prime forces

The renewal kernel and its surviving-prime force live on coprime
indices. Its deleted-prime force vanishes there. Hence the coefficient
energies split exactly, with a half-logarithmic bound for the surviving
part. This coefficient orthogonality does not assert orthogonality after
different arithmetic delays have been added in a time profile.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

theorem ccmEulerRough_of_not_coprime {P n : ℕ} (hn : ¬n.Coprime P) :
    ccmEulerRough P n = 0 := by
  change (if 1 < n ∧ n.Coprime P then (1 : ℝ) else 0) = 0
  simp [hn]

private theorem coprime_convolution_support (P : ℕ) (a b : ArithmeticFunction ℝ)
    (ha : ∀ n, ¬n.Coprime P → a n = 0) (hb : ∀ n, ¬n.Coprime P → b n = 0)
    {n : ℕ} (hn : ¬n.Coprime P) : (a * b) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro de hde
  by_cases hd : de.1.Coprime P
  · have he : ¬de.2.Coprime P := by
      intro he
      exact hn ((Nat.mem_divisorsAntidiagonal.mp hde).1 ▸ hd.mul_left he)
    rw [hb _ he, mul_zero]
  · rw [ha _ hd, zero_mul]

theorem ccmEulerRenewalKernel_of_not_coprime {P n : ℕ} (hn : ¬n.Coprime P) :
    ccmEulerRenewalKernel P n = 0 := by
  rw [ccmEulerRenewalKernel, pow_two]
  exact coprime_convolution_support P _ _ (fun _ h => ccmEulerRough_of_not_coprime h)
    (fun _ h => ccmEulerRough_of_not_coprime h) hn

theorem ccmEulerRenewal_survivingForce_of_not_coprime {P n : ℕ} (hn : ¬n.Coprime P) :
    (ccmEulerRenewalKernel P * ccmEulerSurvivingPrime P : ArithmeticFunction ℝ) n = 0 := by
  exact coprime_convolution_support P _ _ (fun _ h => ccmEulerRenewalKernel_of_not_coprime h)
    (fun j h => by rw [ccmEulerSurvivingPrime_apply, if_neg h]) hn

theorem ccmEulerRenewal_deletedForce_of_coprime {P n : ℕ} (hn : n.Coprime P) :
    (ccmEulerRenewalKernel P * ccmEulerDeletedPrime P : ArithmeticFunction ℝ) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro de hde
  have he : de.2.Coprime P := hn.coprime_dvd_left
    (Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hde))
  rw [ccmEulerDeletedPrime_apply, if_pos he, mul_zero]

/-- The two prime channels are orthogonal before summation over delays. -/
theorem ccmEulerRenewal_prime_force_orthogonal (P n : ℕ) :
    (ccmEulerRenewalKernel P * ccmEulerSurvivingPrime P : ArithmeticFunction ℝ) n *
      (ccmEulerRenewalKernel P * ccmEulerDeletedPrime P : ArithmeticFunction ℝ) n = 0 := by
  by_cases hn : n.Coprime P
  · rw [ccmEulerRenewal_deletedForce_of_coprime hn, mul_zero]
  · rw [ccmEulerRenewal_survivingForce_of_not_coprime hn, zero_mul]

theorem ccmEulerRenewal_prime_force_sq_split (P n : ℕ) :
    (ccmEulerRenewalKernel P * ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n ^ 2 =
      (ccmEulerRenewalKernel P * ccmEulerSurvivingPrime P : ArithmeticFunction ℝ) n ^ 2 +
      (ccmEulerRenewalKernel P * ccmEulerDeletedPrime P : ArithmeticFunction ℝ) n ^ 2 := by
  rw [← ccmEuler_prime_split P, mul_add, ArithmeticFunction.add_apply]
  nlinarith only [ccmEulerRenewal_prime_force_orthogonal P n]

/-- The split survives every finite carrier and every external real weight. -/
theorem ccmEulerRenewal_prime_energy_split (P : ℕ) (I : Finset ℕ) (W : ℕ → ℝ) :
    (∑ n ∈ I, W n * (ccmEulerRenewalKernel P * ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n ^ 2) =
      (∑ n ∈ I, W n * (ccmEulerRenewalKernel P * ccmEulerSurvivingPrime P : ArithmeticFunction ℝ) n ^ 2) +
      ∑ n ∈ I, W n * (ccmEulerRenewalKernel P * ccmEulerDeletedPrime P : ArithmeticFunction ℝ) n ^ 2 := by
  simp_rw [ccmEulerRenewal_prime_force_sq_split, mul_add, Finset.sum_add_distrib]

/-- Critical coefficient energy of surviving force is bounded by one
quarter of the exact logarithmic-moment energy. -/
theorem ccmEulerRenewal_surviving_energy_le_logMoment (P : ℕ) (I : Finset ℕ) :
    (∑ n ∈ I, (ccmEulerRenewalKernel P * ccmEulerSurvivingPrime P : ArithmeticFunction ℝ) n ^ 2 / n) ≤
      (1 / 4 : ℝ) * ∑ n ∈ I, (ccmEulerRenewalKernel P n * Real.log n) ^ 2 / n := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  have h0 : 0 ≤ (ccmEulerRenewalKernel P * ccmEulerSurvivingPrime P : ArithmeticFunction ℝ) n := by
    rw [ArithmeticFunction.mul_apply]
    exact Finset.sum_nonneg fun de _ => mul_nonneg (ccmEulerRenewalKernel_nonneg P de.1)
      (ccmEulerSurvivingPrime_nonneg P de.2)
  calc
    _ ≤ (ccmEulerRenewalKernel P n * Real.log n / 2) ^ 2 / n := by
      gcongr
      exact ccmEulerRenewal_survivingForce_le_half_log P n
    _ = _ := by ring

end RHTower
