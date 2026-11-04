import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.LiteralUpwardRowMass
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.UpwardProfileNorms
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# Physical upward norm of bounded arithmetic profiles

The exact reciprocal row formula and harmonic mass bound retain both
offset signs and every finite horizon cutoff.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open GaloisForLFunctions.ArithmeticCouplingTheory
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- A bounded arithmetic profile has a uniform physical upward norm controlled by its strip width. -/
theorem upward_physical_bounded_profile_norm_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hlog : 1 ≤ Real.log N) (hwidth : c / N ≤ 1)
    (hB : linearPrimeStrip c ≤ N)
    (hsep : 2 * c * Real.exp 1 * linearPrimeStrip c ≤ N)
    (F : ℕ → ℝ) {V : ℝ} (hV : 0 ≤ V) (hF : ∀ j, |F j| ≤ V) :
    ‖upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ • packetVector F N)‖ ≤
      8 * (linearPrimeStrip c : ℝ) * V *
        (|Real.log (2 * c * Real.exp 1)| + mertensWindowConstant + 1) := by
  let C : ℝ := 4 * (linearPrimeStrip c : ℝ) * V *
    (|Real.log (2 * c * Real.exp 1)| + mertensWindowConstant + 1)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hV)
      (add_nonneg (add_nonneg (abs_nonneg _) mertensWindowConstant_nonneg) zero_le_one)
  have hL : 0 < Real.log N := lt_of_lt_of_le zero_lt_one hlog
  have hsum :
      (∑ n ∈ Icc 1 N, logarithmicUpwardProfileCoefficient φ c (linearPrimeStrip c) N F n ^ 2 /
        (n : ℝ)) ≤ C ^ 2 * (1 + Real.log N) := by
    calc
      _ ≤ C ^ 2 * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := by
        rw [mul_sum]
        apply sum_le_sum
        intro n hn
        have h := pow_le_pow_left₀ (abs_nonneg _)
          (abs_logarithmicUpwardProfileCoefficient_le hφ hsupp hM hc hn hwidth hB hsep F hV hF) 2
        rw [sq_abs] at h
        exact (div_le_div_of_nonneg_right h (Nat.cast_nonneg n)).trans_eq (by ring)
      _ ≤ _ := mul_le_mul_of_nonneg_left (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log N)
        (sq_nonneg C)
  have hsq :
      ‖upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ • packetVector F N)‖ ^ 2 ≤ 2 * C ^ 2 := by
    rw [upwardPrimeVector_physical_packet_norm_sq hsupp hc hwidth]
    refine (div_le_div_of_nonneg_right hsum hL.le).trans ?_
    apply (div_le_iff₀ hL).mpr
    have h := mul_nonneg (sq_nonneg C) (sub_nonneg.mpr hlog)
    nlinarith only [h]
  have hnorm :
      ‖upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ • packetVector F N)‖ ≤ 2 * C := by
    nlinarith only [hsq, hC, sq_nonneg C,
      norm_nonneg (upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ • packetVector F N))]
  exact hnorm.trans_eq (by dsimp only [C]; ring)

#print axioms upward_physical_bounded_profile_norm_le

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
