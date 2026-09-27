import GaloisForLFunctions.RHTower.CCMPrimeDeficitEulerDeletedChannels
import GaloisForLFunctions.RHTower.Sieve.CriticalDivisorAffineMeanSquare

/-!
# The finite energy budget of deleted prime towers

For a positive Euler modulus the deleted von Mangoldt sequence has bounded
critical coefficient energy, independently of the truncation horizon.
The exact square-convolution identity transfers this budget to the renewal
force, with the fourth harmonic divisor moment as its remaining cost.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

/-- Total geometric energy of the prime-power towers dividing the modulus. -/
def ccmEulerDeletedEnergyBudget (P : ℕ) : ℝ :=
  ∑ p ∈ P.primeFactors, (Real.log p) ^ 2 / ((p : ℝ) - 1)

theorem ccmEulerDeletedEnergyBudget_nonneg (P : ℕ) :
    0 ≤ ccmEulerDeletedEnergyBudget P := by
  apply Finset.sum_nonneg
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  exact div_nonneg (sq_nonneg _) (by linarith)

private theorem deleted_energy_le_towers (P N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ccmEulerDeletedPrime (P + 1) n ^ 2 / n) ≤
      ∑ p ∈ (P + 1).primeFactors, ∑ k ∈ Finset.Icc 1 N,
        (Real.log p) ^ 2 / ((p : ℝ) ^ k) := by
  classical
  have hpoint : ∀ n ∈ Finset.Icc 1 N,
      ccmEulerDeletedPrime (P + 1) n ^ 2 / n ≤
        ∑ p ∈ (P + 1).primeFactors, ∑ k ∈ Finset.Icc 1 N,
          if p ^ k = n then (Real.log p) ^ 2 / ((p : ℝ) ^ k) else 0 := by
    intro n hn
    by_cases hz : ccmEulerDeletedPrime (P + 1) n = 0
    · rw [hz, zero_pow two_ne_zero, zero_div]
      positivity
    obtain ⟨hpow, hcop⟩ := (ccmEulerDeletedPrime_ne_zero_iff (P + 1) n).mp hz
    obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff n).mp hpow
    have hpP : p ∣ P + 1 := by
      by_contra h
      exact hcop (hpk ▸ (hp.coprime_iff_not_dvd.mpr h).pow_left k)
    have hpmem : p ∈ (P + 1).primeFactors := hp.mem_primeFactors hpP (Nat.succ_ne_zero P)
    have hkmem : k ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr
      ⟨hk, (hpk ▸ (Nat.lt_pow_self hp.one_lt : k < p ^ k)).le.trans (Finset.mem_Icc.mp hn).2⟩
    calc
      _ = (Real.log p) ^ 2 / ((p : ℝ) ^ k) := by
        rw [ccmEulerDeletedPrime_apply, if_neg hcop, ← hpk,
          ArithmeticFunction.vonMangoldt_apply_pow hk.ne', ArithmeticFunction.vonMangoldt_apply_prime hp,
          Nat.cast_pow]
      _ ≤ ∑ j ∈ Finset.Icc 1 N,
          if p ^ j = n then (Real.log p) ^ 2 / ((p : ℝ) ^ j) else 0 := by
        simpa only [if_pos hpk] using
          (Finset.single_le_sum (f := fun j =>
            if p ^ j = n then (Real.log p) ^ 2 / ((p : ℝ) ^ j) else 0)
            (fun j _ => by positivity) hkmem)
      _ ≤ _ := Finset.single_le_sum
        (f := fun q => ∑ j ∈ Finset.Icc 1 N,
          if q ^ j = n then (Real.log q) ^ 2 / ((q : ℝ) ^ j) else 0)
        (fun q _ => Finset.sum_nonneg fun j _ => by positivity) hpmem
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ (P + 1).primeFactors, ∑ k ∈ Finset.Icc 1 N,
        if p ^ k = n then (Real.log p) ^ 2 / ((p : ℝ) ^ k) else 0 :=
      Finset.sum_le_sum hpoint
    _ = ∑ p ∈ (P + 1).primeFactors, ∑ k ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        if p ^ k = n then (Real.log p) ^ 2 / ((p : ℝ) ^ k) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro k _
      simp only [Finset.sum_ite_eq]
      split_ifs
      · exact le_rfl
      · positivity

private theorem prime_tower_energy_le {p : ℕ} (hp : p.Prime) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, (Real.log p) ^ 2 / ((p : ℝ) ^ k)) ≤
      (Real.log p) ^ 2 / ((p : ℝ) - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hi0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hp0.le
  have hi1 : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hp1
  calc
    _ = (Real.log p) ^ 2 * ∑ k ∈ Finset.Ico 1 (N + 1), ((p : ℝ)⁻¹) ^ k := by
      rw [Finset.mul_sum, show Finset.Ico 1 (N + 1) = Finset.Icc 1 N from by
        ext k
        simp only [Finset.mem_Ico, Finset.mem_Icc]
        omega]
      apply Finset.sum_congr rfl
      intro k _
      simp only [div_eq_mul_inv, inv_pow]
    _ ≤ (Real.log p) ^ 2 * (((p : ℝ)⁻¹) ^ 1 / (1 - (p : ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hi0 hi1) (sq_nonneg _)
    _ = _ := by
      rw [pow_one]
      field_simp

/-- A fixed positive modulus has a finite deleted-prime critical energy budget. -/
theorem ccmEulerDeletedPrime_critical_energy_le (P N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ccmEulerDeletedPrime (P + 1) n ^ 2 / n) ≤
      ccmEulerDeletedEnergyBudget (P + 1) := by
  apply (deleted_energy_le_towers P N).trans
  exact Finset.sum_le_sum fun p hp => prime_tower_energy_le (Nat.prime_of_mem_primeFactors hp) N

/-- Exact triangular factorization of the deleted-force energy. -/
theorem ccmEulerRenewal_deletedForce_energy_eq (P N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      (ccmEulerRenewalKernel P * ccmEulerDeletedPrime P : ArithmeticFunction ℝ) n ^ 2 / n) =
      ∑ a ∈ Finset.Icc 1 N, ccmEulerRenewalKernel P a ^ 2 / a *
        ∑ b ∈ Finset.Icc 1 (N / a), ccmEulerDeletedPrime P b ^ 2 / b := by
  simp only [ccmEulerRenewal_deletedForce_sq, Finset.sum_div, Finset.mul_sum]
  have he : (∑ n ∈ Finset.Icc 1 N, ∑ ab ∈ n.divisorsAntidiagonal,
      ccmEulerRenewalKernel P ab.1 ^ 2 * ccmEulerDeletedPrime P ab.2 ^ 2 / n) =
      ∑ n ∈ Finset.Icc 1 N, ∑ ab ∈ n.divisorsAntidiagonal,
        (ccmEulerRenewalKernel P ab.1 ^ 2 / ab.1) * (ccmEulerDeletedPrime P ab.2 ^ 2 / ab.2) := by
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro ab hab
    rw [← (Nat.mem_divisorsAntidiagonal.mp hab).1, Nat.cast_mul, div_mul_div_comm]
  rw [he]
  exact Sieve.sum_Icc_divisorsAntidiagonal_swap
    (fun a b => ccmEulerRenewalKernel P a ^ 2 / a * (ccmEulerDeletedPrime P b ^ 2 / b)) N

/-- Horizon-uniform tower energy times the remaining rough coefficient energy. -/
theorem ccmEulerRenewal_deletedForce_energy_le_budget (P N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      (ccmEulerRenewalKernel (P + 1) * ccmEulerDeletedPrime (P + 1) : ArithmeticFunction ℝ) n ^ 2 / n) ≤
      ccmEulerDeletedEnergyBudget (P + 1) *
        ∑ a ∈ Finset.Icc 1 N, ccmEulerRenewalKernel (P + 1) a ^ 2 / a := by
  rw [ccmEulerRenewal_deletedForce_energy_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [mul_comm (ccmEulerDeletedEnergyBudget (P + 1))]
  exact mul_le_mul_of_nonneg_left (ccmEulerDeletedPrime_critical_energy_le P (N / a))
    (by positivity)

end RHTower
