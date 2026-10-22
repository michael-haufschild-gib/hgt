import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspMiddleLikelihoodBounds
import GaloisForLFunctions.HTGeometry.TwoAtomOddLowerReserve

/-! # Actual-source admission to the two-atom polynomial reserve regions -/
namespace RHTower
noncomputable section
set_option maxHeartbeats 1500000

private theorem exp_eleven_tenths_calibration : (65000 : ℝ) ≤ Real.exp (111/10) := by
  have h1 : (2718/1000 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num) h1 11
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have ht : (11/10 : ℝ) ≤ Real.exp (1/10) := by linarith [Real.add_one_le_exp (1/10)]
  have hm := mul_le_mul hp ht (by norm_num : (0 : ℝ) ≤ 11/10) (Real.exp_pos 11).le
  rw [← Real.exp_add] at hm
  norm_num at hm
  linarith only [hm]

/-- The actual relative second Gaussian satisfies the coupled quadratic envelope. -/
theorem thetaCuspTwoAtom_lower_envelope_admission {q : ℝ} (hq : 37/10 ≤ q) :
    HTGeometry.twoAtomLowerEnvelope q*Real.exp (-3*q) ≤ 1 := by
  have ht : 0 ≤ 3*(q-37/10) := by linarith
  have he := Real.sum_le_exp_of_nonneg ht 3
  norm_num [Finset.sum_range_succ] at he
  have hpoly : 1+3*(q-37/10)+(9/2)*(q-37/10)^(2 : ℕ) ≤ Real.exp (3*(q-37/10)) := by
    nlinarith only [he]
  have hp : 0 ≤ 1+3*(q-37/10)+(9/2)*(q-37/10)^(2 : ℕ) := by
    have : 0 ≤ q-37/10 := by linarith
    positivity
  have hm := mul_le_mul exp_eleven_tenths_calibration hpoly hp (Real.exp_pos (111/10)).le
  rw [← Real.exp_add, show (111/10 : ℝ)+3*(q-37/10) = 3*q by ring] at hm
  have hb := mul_le_mul_of_nonneg_right hm (Real.exp_pos (-3*q)).le
  rw [← Real.exp_add, show 3*q+(-3*q) = 0 by ring, Real.exp_zero] at hb
  exact hb

/-- Scale five admits the full relative second Gaussian to its fixed upper-middle box. -/
theorem thetaCuspTwoAtom_high_envelope_admission {q : ℝ} (hq : 5 ≤ q) :
    Real.exp (-3*q) ≤ 1/3000000 := by
  have h1 : (271/100 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num) h1 15
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have he := hp.trans (Real.exp_le_exp.mpr (show (15 : ℝ) ≤ 3*q by linarith))
  have he' : (3000000 : ℝ) ≤ Real.exp (3*q) := by linarith only [he]
  rw [show -3*q = -(3*q) by ring, Real.exp_neg]
  simpa only [one_div] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3000000) he'

end
end RHTower
