import GaloisForLFunctions.RHTower.ThetaCuspDeepTailCalibration
import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomExponentialAdmission

/-! # Polynomial-weighted complete tail bounds on the middle scale -/
namespace RHTower
noncomputable section

private theorem exp_ten_calibration : (21000 : ℝ) ≤ Real.exp 10 := by
  have h1 : (271/100 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num) h1 10
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  linarith only [hp]

/-- The calibrated full tail absorbs every scale power required by the odd determinant. -/
theorem thetaCuspDeepTailErrorScale_weighted_middle {k : ℕ} (hk : k ≤ 5) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspSingleAtomReflectionScale 1 x^k*thetaCuspDeepTailErrorScale x ≤
      (37/10 : ℝ)^k/21000000000 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hkr : (k : ℝ) ≤ 5 := by exact_mod_cast hk
  have hp := pow_mul_exp_neg_le_of_le (m := k) (δ := 8) (a := (37/10 : ℝ))
    (t := q) (by norm_num) (by linarith) hq
  have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (98/5)).le
  have heq (t : ℝ) : Real.exp (-(8*t))*Real.exp (98/5) = Real.exp (-8*(t-49/20)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [mul_assoc, heq] at hm
  norm_num at hm
  have he : Real.exp (-(10 : ℝ)) ≤ 1/21000 := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 21000)
      exp_ten_calibration
  have hfinal := hm.trans (mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ (37/10)^k))
  change q^k*(Real.exp (-8*(q-49/20))/1000000) ≤ _
  simp only [neg_mul] at hfinal ⊢
  nlinarith only [hfinal]

/-- Every actual relative second Gaussian lies in the static box used for entry bounds. -/
theorem thetaCuspTwoAtom_middle_envelope_admission {q : ℝ} (hq : 37/10 ≤ q) :
    Real.exp (-3*q) ≤ 1/65000 := by
  have h := thetaCuspTwoAtom_lower_envelope_admission hq
  have he : (65000 : ℝ) ≤ HTGeometry.twoAtomLowerEnvelope q := by
    unfold HTGeometry.twoAtomLowerEnvelope
    nlinarith [sq_nonneg (q-37/10)]
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-3*q)).le
  linarith

end
end RHTower
