import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeMoments
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The exact divisor mean of a coherent prime charge

Harmonic centering changes only conductor one. On every other conductor,
the divisor-weighted coefficient square reduces to `(t/B)²(p+1)/p²`.
Thus the near-Gram divisor mean retains the reciprocal-prime gain.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open SelectiveMultiscaleArithmeticPositivity

/-- Harmonic pole removal preserves every nonpolar coefficient. -/
theorem harmonicPrimeCharge_nonpolar_coefficient (Q N : ℕ) (t : ℝ)
    {m : ℕ} (hm : m ≠ 1) :
    harmonicPrimeChargeCoefficients Q N t m =
      if m.Prime then (t / primePoleScale Q) * primePoleWitness m else 0 := by
  simp only [harmonicPrimeChargeCoefficients, harmonicCenteredCoefficients,
    addConstantConductor, if_neg hm, primeOnly]

private theorem sigma_one_prime {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.sigma 1 p = p + 1 := by
  simpa only [pow_one, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, zero_add, add_comm] using
    ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp

/-- Each prime contributes its reciprocal plus its reciprocal square to the divisor mean. -/
theorem primePoleWitness_sq_mul_divisorMean {p : ℕ} (hp : p.Prime) :
    primePoleWitness p ^ 2 * ((ArithmeticFunction.sigma 1 p : ℝ) / p.totient) =
      ((p : ℝ) + 1) / (p : ℝ) ^ 2 := by
  rw [primePoleWitness, div_pow, Real.sq_sqrt (Nat.cast_nonneg _),
    sigma_one_prime hp, Nat.cast_add, Nat.cast_one]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hφ : (p.totient : ℝ) ≠ 0 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
    linarith only [hp2]
  field_simp [hφ]

/-- The nonpolar divisor mean of the exactly neutral charge has an exact prime-sum formula. -/
theorem harmonicPrimeCharge_nonpolar_divisorMean (Q N : ℕ) (t : ℝ) :
    (∑ m ∈ (Icc 1 Q).filter (fun m => m ≠ 1),
      harmonicPrimeChargeCoefficients Q N t m ^ 2 *
        ((ArithmeticFunction.sigma 1 m : ℝ) / m.totient)) =
      (t / primePoleScale Q) ^ 2 *
        ∑ p ∈ (Icc 1 Q).filter Nat.Prime, ((p : ℝ) + 1) / (p : ℝ) ^ 2 := by
  rw [sum_filter, mul_sum, sum_filter]
  apply sum_congr rfl
  intro m _
  by_cases hp : m.Prime
  · have hm := hp.ne_one
    rw [if_pos hm, if_pos hp, harmonicPrimeCharge_nonpolar_coefficient Q N t hm,
      if_pos hp, mul_pow, mul_assoc, primePoleWitness_sq_mul_divisorMean hp]
  · by_cases hm : m = 1
    · simp only [hm, if_false, if_neg Nat.not_prime_one, Ne, not_true_eq_false]
    · rw [if_pos hm, if_neg hp, harmonicPrimeCharge_nonpolar_coefficient Q N t hm,
        if_neg hp, zero_pow two_ne_zero, zero_mul]

/-- Coherent nonpolar divisor cost is bounded by three halves of its reciprocal-prime mass. -/
theorem harmonicPrimeCharge_nonpolar_divisorMean_le (Q N : ℕ) (t : ℝ) :
    (∑ m ∈ (Icc 1 Q).filter (fun m => m ≠ 1),
      harmonicPrimeChargeCoefficients Q N t m ^ 2 *
        ((ArithmeticFunction.sigma 1 m : ℝ) / m.totient)) ≤
      (3 / 2 : ℝ) * (t / primePoleScale Q) ^ 2 *
        ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ) := by
  rw [harmonicPrimeCharge_nonpolar_divisorMean]
  have hsum : (∑ p ∈ (Icc 1 Q).filter Nat.Prime, ((p : ℝ) + 1) / (p : ℝ) ^ 2) ≤
      (3 / 2 : ℝ) * ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
    have hp0 : (0 : ℝ) < p := by linarith only [hp2]
    apply (div_le_iff₀ (sq_pos_of_pos hp0)).mpr
    have he : (3 / 2 * (1 / (p : ℝ))) * (p : ℝ) ^ 2 = 3 / 2 * p := by
      field_simp [hp0.ne']
    rw [he]
    linarith only [hp2]
  exact (mul_le_mul_of_nonneg_left hsum (sq_nonneg _)).trans_eq (by ring)

#print axioms harmonicPrimeCharge_nonpolar_divisorMean
#print axioms harmonicPrimeCharge_nonpolar_divisorMean_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
