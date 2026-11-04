import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeDivisorMean
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargePoleCoefficient
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeCompleteEnergy
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.PhysicalHorizonCharges
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonCountertermIsPolar

/-!
# Uniform coefficient costs of a neutral coherent charge

The polar coefficient costs one inverse harmonic horizon. Nonpolar
coefficient squares keep their reciprocal-prime weights, including after
insertion of the logarithmic conductor weight.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open SelectiveMultiscaleArithmeticPositivity

/-- Exact centering has a pole coefficient of size at most the charge divided by the horizon logarithm. -/
theorem harmonicPrimeCharge_pole_abs_le {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q ≤ N) (t : ℝ) :
    |harmonicPrimeChargeCoefficients Q N t 1| ≤
      (|t| + 8 * |t| / primePoleScale Q) / Real.log N := by
  have hN : 1 ≤ N := by omega
  have hH := harmonicMass_pos hN
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hLH : Real.log N ≤ harmonicMass N :=
    RenormalizedArithmeticPotentialTheory.log_le_harmonicSum N
  have hnum : 0 ≤ |t| + 8 * |t| / primePoleScale Q := by
    have hB := primePoleScale_pos hQ
    positivity
  have h := (abs_add_le
    (harmonicMass N * harmonicPrimeChargeCoefficients Q N t 1 - t) t).trans
      (add_le_add (harmonicPrimeCharge_pole_error_uniform hQ hQN t) le_rfl)
  rw [sub_add_cancel, abs_mul, abs_of_pos hH] at h
  have ha : |harmonicPrimeChargeCoefficients Q N t 1| ≤
      (|t| + 8 * |t| / primePoleScale Q) / harmonicMass N := by
    apply (le_div_iff₀ hH).mpr
    linarith only [h]
  exact ha.trans (div_le_div_of_nonneg_left hnum hL hLH)

private theorem primePoleWitness_sq_le_inv {p : ℕ} (hp : p.Prime) :
    primePoleWitness p ^ 2 ≤ 1 / (p : ℝ) := by
  rw [primePoleWitness, div_pow, Real.sq_sqrt (Nat.cast_nonneg _),
    Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  apply (div_le_iff₀ (sq_pos_of_pos hp0)).mpr
  have he : (1 / (p : ℝ)) * (p : ℝ) ^ 2 = p := by field_simp [hp0.ne']
  rw [he]
  linarith

/-- Every nonnegative prime weight preserves the reciprocal-prime coefficient gain. -/
theorem harmonicPrimeCharge_nonpolar_weighted_sq_le (Q N : ℕ) (t : ℝ)
    (w : ℕ → ℝ) (hw : ∀ p ∈ (Icc 1 Q).filter Nat.Prime, 0 ≤ w p) :
    (∑ m ∈ (Icc 1 Q).filter (fun m => m ≠ 1),
      w m * harmonicPrimeChargeCoefficients Q N t m ^ 2) ≤
      (t / primePoleScale Q) ^ 2 * ∑ p ∈ (Icc 1 Q).filter Nat.Prime, w p / p := by
  rw [sum_filter, mul_sum, sum_filter]
  apply sum_le_sum
  intro m hmQ
  by_cases hp : m.Prime
  · have hm := hp.ne_one
    rw [if_pos hm, if_pos hp, harmonicPrimeCharge_nonpolar_coefficient Q N t hm,
      if_pos hp, mul_pow]
    have h := mul_le_mul_of_nonneg_left (primePoleWitness_sq_le_inv hp)
      (mul_nonneg (hw m (mem_filter.mpr ⟨hmQ, hp⟩)) (sq_nonneg (t / primePoleScale Q)))
    convert h using 1 <;> ring
  · by_cases hm : m = 1
    · simp only [hm, if_false, if_neg Nat.not_prime_one, Ne, not_true_eq_false, le_refl]
    · rw [if_pos hm, if_neg hp, harmonicPrimeCharge_nonpolar_coefficient Q N t hm,
        if_neg hp, zero_pow two_ne_zero, mul_zero]

/-- The logarithmically weighted nonpolar square is bounded by reciprocal mass plus prime Mertens mass. -/
theorem harmonicPrimeCharge_nonpolar_log_sq_le (Q N : ℕ) (t : ℝ) :
    (∑ m ∈ (Icc 1 Q).filter (fun m => m ≠ 1),
      (1 + Real.log m) * harmonicPrimeChargeCoefficients Q N t m ^ 2) ≤
      (t / primePoleScale Q) ^ 2 *
        ((∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) + primePoleScale Q) := by
  have h := harmonicPrimeCharge_nonpolar_weighted_sq_le Q N t
    (fun m => 1 + Real.log m) (fun m _ => by linarith only [Real.log_natCast_nonneg m])
  simpa only [add_div, sum_add_distrib, primePoleScale] using h

/-- Physical sampling preserves the reciprocal-prime gain uniformly above the cutoff. -/
theorem harmonicPrimeChargeVector_norm_sq_le {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q ≤ N) (t : ℝ) :
    ‖harmonicPrimeChargeVector Q N t‖ ^ 2 ≤
      52 * (t / primePoleScale Q) ^ 2 *
        ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ) := by
  let b := primeOnly (fun p => (t / primePoleScale Q) * primePoleWitness p)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hproj := harmonicCentered_profile_sq_le (by omega : 1 ≤ Q) (by omega : 1 ≤ N) b
  simp only [conductorHorizonProfile, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at hproj
  have hmass : (∑ p ∈ Icc 1 Q, b p ^ 2) ≤
      (t / primePoleScale Q) ^ 2 * ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ) := by
    rw [mul_sum, sum_filter]
    apply sum_le_sum
    intro p _
    by_cases hp : p.Prime
    · simp only [b, primeOnly, if_pos hp, mul_pow]
      exact mul_le_mul_of_nonneg_left (primePoleWitness_sq_le_inv hp) (sq_nonneg _)
    · simp only [b, primeOnly, if_neg hp, zero_pow two_ne_zero, le_refl]
  rw [harmonicPrimeChargeVector_norm_sq, ArithmeticCouplingTheory.packetVector_norm_sq]
  exact (div_le_div_of_nonneg_right hproj hL.le).trans
    ((harmonicPacket_sq_div_log_le_mass hQ hQN b).trans
      ((mul_le_mul_of_nonneg_left hmass (by norm_num : (0 : ℝ) ≤ 52)).trans_eq (by ring)))

#print axioms harmonicPrimeCharge_pole_abs_le
#print axioms harmonicPrimeCharge_nonpolar_log_sq_le
#print axioms harmonicPrimeChargeVector_norm_sq_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
