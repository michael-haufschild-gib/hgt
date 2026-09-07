import GaloisForLFunctions.RHTower.ThetaCuspDeepTailCalibration

/-! # Calibrated deep-tail support transport with a movable comparison radius -/
namespace RHTower
noncomputable section
open MeasureTheory

/-- Increasing the comparison radius retains the original exponential support edge. -/
theorem pow_mul_exp_neg_le_shifted_support {n : ℕ} {d a b t : ℝ}
    (hb : 0 < b) (hba : b ≤ a) (hbt : b ≤ t) (hd : (n : ℝ)/a ≤ d) :
    t^n*Real.exp (-(d*t)) ≤ a^n*Real.exp (-(d*b)) := by
  have ha : 0 < a := hb.trans_le hba
  have ht : 0 ≤ t := hb.le.trans hbt
  have hpow : t^n ≤ (t+a-b)^n := pow_le_pow_left₀ ht (by linarith) n
  have hkey := pow_mul_exp_neg_le_of_le (m := n) (δ := d) (a := a)
    (t := t+a-b) ha hd (by linarith)
  have hm := mul_le_mul_of_nonneg_right hkey (Real.exp_pos (d*(a-b))).le
  have hl : ((t+a-b)^n*Real.exp (-(d*(t+a-b))))*Real.exp (d*(a-b)) =
      (t+a-b)^n*Real.exp (-(d*t)) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hr : (a^n*Real.exp (-(d*a)))*Real.exp (d*(a-b)) =
      a^n*Real.exp (-(d*b)) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hl, hr] at hm
  exact (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le).trans hm

/-- Every deep-tail moment admits support transport beyond the sharp-radius order cutoff. -/
theorem thetaCuspDeepTailMoment_le_radius_support_comparison (n : ℕ) {a B₀ B : ℝ}
    (ha : 8 ≤ a) (hB₀ : 0 < B₀) (hd : (n : ℝ)/a ≤ B-B₀) :
    thetaCuspDeepTailMoment B n ≤
      a^n*Real.exp (-(8*(B-B₀)))*thetaCuspDeepTailMoment B₀ 0 := by
  have hap : 0 < a := by linarith
  have hn : (0 : ℝ) ≤ (n : ℝ)/a := div_nonneg (Nat.cast_nonneg n) hap.le
  have hB : 0 < B := by linarith
  unfold thetaCuspDeepTailMoment
  rw [← integral_const_mul]
  apply integral_mono_ae
    (integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure n hB)
    ((integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure 0 hB₀).const_mul _)
  filter_upwards [ae_eight_le_thetaCuspDeepTailSpectralMeasure] with t ht
  simp only [pow_zero, one_mul]
  have hkey := pow_mul_exp_neg_le_shifted_support (n := n) (d := B-B₀)
    (a := a) (b := 8) (t := t) (by norm_num) ha ht hd
  have hs : Real.exp (-B*t) = Real.exp (-((B-B₀)*t))*Real.exp (-B₀*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hs, ← mul_assoc]
  convert mul_le_mul_of_nonneg_right hkey (Real.exp_pos (-B₀*t)).le using 1
  ring_nf

/-- A movable radius keeps the existing complete-source calibration and decay rate. -/
theorem thetaCuspDeepTailMoment_le_radius_errorScale (n : ℕ) {a x : ℝ}
    (ha : 8 ≤ a) (hn : (n : ℝ)/a ≤ thetaCuspSingleAtomReflectionScale 1 x-49/20) :
    thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x) n ≤
      a^n*thetaCuspDeepTailErrorScale x := by
  have hc : thetaCuspLikelihoodCoordinate x-19/20 =
      thetaCuspSingleAtomReflectionScale 1 x-49/20 := by
    have h := thetaCuspLikelihoodCoordinate_sub_zero x
    have h0 := thetaCuspLikelihoodCoordinate_zero_eq
    linarith
  have hd : (n : ℝ)/a ≤ thetaCuspLikelihoodCoordinate x-19/20 := by rwa [hc]
  have h := thetaCuspDeepTailMoment_le_radius_support_comparison n ha
    (by norm_num : (0 : ℝ) < 19/20) hd
  rw [hc] at h
  have hap : 0 ≤ a := by linarith
  have hm := mul_le_mul_of_nonneg_left thetaCuspDeepTailMoment_calibration
    (show 0 ≤ a^n*Real.exp (-(8*(thetaCuspSingleAtomReflectionScale 1 x-49/20))) by positivity)
  unfold thetaCuspDeepTailErrorScale
  simp only [neg_mul] at h hm ⊢
  nlinarith only [h, hm]

/-- The original middle interval admits all moments through twelve with radius forty-eight fifths. -/
theorem thetaCuspDeepTailMoment_le_errorScale_twelve {n : ℕ} (hn : n ≤ 12) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x) n ≤
      (48/5 : ℝ)^n*thetaCuspDeepTailErrorScale x := by
  apply thetaCuspDeepTailMoment_le_radius_errorScale n (by norm_num)
  have hnr : (n : ℝ) ≤ 12 := by exact_mod_cast hn
  linarith

end
end RHTower
