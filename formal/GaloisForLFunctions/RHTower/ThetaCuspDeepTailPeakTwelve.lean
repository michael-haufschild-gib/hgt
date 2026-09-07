import GaloisForLFunctions.RHTower.ThetaCuspDeepTailExtendedSupport

/-! # Peak-sensitive complete deep-tail moments at orders eleven and twelve -/
namespace RHTower
noncomputable section
open MeasureTheory

/-- The stationary radius bounds a polynomial-exponential profile on its whole nonnegative ray. -/
theorem pow_mul_exp_neg_le_stationary_radius (n : ℕ) {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    t^n*Real.exp (-((n : ℝ)/a*t)) ≤ a^n*Real.exp (-(n : ℝ)) := by
  have hq : t/a ≤ Real.exp (t/a-1) := by linarith [Real.add_one_le_exp (t/a-1)]
  have hp := pow_le_pow_left₀ (div_nonneg ht ha.le) hq n
  rw [← Real.exp_nat_mul] at hp
  have hsplit : t^n = a^n*(t/a)^n := by rw [← mul_pow, mul_div_cancel₀ _ ha.ne']
  rw [hsplit, mul_assoc]
  calc
    _ ≤ a^n*(Real.exp ((n : ℝ)*(t/a-1))*Real.exp (-((n : ℝ)/a*t))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le)
        (pow_nonneg ha.le n)
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

private theorem exp_neg_one_bound : Real.exp (-1 : ℝ) ≤ 10/27 := by
  have he : (27/10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  rw [Real.exp_neg]
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 27/10) he
  norm_num at h
  exact h

private theorem peak_eleven {t : ℝ} (ht : 0 ≤ t) :
    t^11*Real.exp (-(5/4*t)) ≤ (5/4 : ℝ)*8^11*Real.exp (-10) := by
  have hp := pow_mul_exp_neg_le_stationary_radius 11 (a := 44/5) (t := t) (by norm_num) ht
  norm_num only [Nat.cast_ofNat, div_div, div_mul_eq_mul_div] at hp
  rw [show -(5*t/4) = -(5/4*t) by ring] at hp
  have hs : Real.exp (-11 : ℝ) = Real.exp (-10)*Real.exp (-1) := by rw [← Real.exp_add]; norm_num
  rw [hs] at hp
  have he := mul_le_mul_of_nonneg_left exp_neg_one_bound
    (show 0 ≤ (44/5 : ℝ)^11*Real.exp (-10) by positivity)
  have hc : (44/5 : ℝ)^11*(10/27) ≤ (5/4)*8^11 := by norm_num
  have hm := mul_le_mul_of_nonneg_right hc (Real.exp_pos (-10)).le
  nlinarith only [hp, he, hm]

private theorem peak_twelve {t : ℝ} (ht : 0 ≤ t) :
    t^12*Real.exp (-(5/4*t)) ≤ (5/4 : ℝ)*8^12*Real.exp (-10) := by
  have hp := pow_mul_exp_neg_le_stationary_radius 12 (a := 48/5) (t := t) (by norm_num) ht
  norm_num only [Nat.cast_ofNat, div_div, div_mul_eq_mul_div] at hp
  rw [show -(5*t/4) = -(5/4*t) by ring] at hp
  have hs : Real.exp (-12 : ℝ) = Real.exp (-10)*Real.exp (-1)^2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
  rw [hs] at hp
  have he2 := pow_le_pow_left₀ (Real.exp_pos (-1)).le exp_neg_one_bound 2
  have he := mul_le_mul_of_nonneg_left he2
    (show 0 ≤ (48/5 : ℝ)^12*Real.exp (-10) by positivity)
  have hc : (48/5 : ℝ)^12*(10/27)^2 ≤ (5/4)*8^12 := by norm_num
  have hm := mul_le_mul_of_nonneg_right hc (Real.exp_pos (-10)).le
  nlinarith only [hp, he, hm]

/-- At either new derivative order the support-edge moment estimate loses at most one quarter. -/
theorem thetaCuspDeepTailMoment_le_errorScale_peak {n : ℕ} (hn : n = 11 ∨ n = 12) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x) n ≤
      (5/4 : ℝ)*8^n*thetaCuspDeepTailErrorScale x := by
  let B := thetaCuspLikelihoodCoordinate x
  let d := thetaCuspSingleAtomReflectionScale 1 x-49/20
  have hc : B = d+19/20 := by
    have h := thetaCuspLikelihoodCoordinate_sub_zero x
    have h0 := thetaCuspLikelihoodCoordinate_zero_eq
    dsimp [B, d]
    linarith
  have hd : 5/4 ≤ d := by dsimp [d]; linarith
  have hB : 0 < B := by linarith
  have hmass : thetaCuspDeepTailMoment B n ≤
      ((5/4 : ℝ)*8^n*Real.exp (-(8*d)))*thetaCuspDeepTailMoment (19/20) 0 := by
    unfold thetaCuspDeepTailMoment
    rw [← integral_const_mul]
    apply integral_mono_ae (integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure n hB)
      ((integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure 0 (by norm_num : (0 : ℝ) < 19/20)).const_mul _)
    filter_upwards [ae_eight_le_thetaCuspDeepTailSpectralMeasure] with t ht
    simp only [pow_zero, one_mul]
    have hp : t^n*Real.exp (-(5/4*t)) ≤ (5/4 : ℝ)*8^n*Real.exp (-10) := by
      rcases hn with rfl | rfl
      · exact peak_eleven (by linarith)
      · exact peak_twelve (by linarith)
    have he : Real.exp (-((d-5/4)*t)) ≤ Real.exp (-(8*(d-5/4))) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hm := mul_le_mul hp he (Real.exp_pos _).le (by positivity)
    have hm' := mul_le_mul_of_nonneg_right hm (Real.exp_pos (-(19/20)*t)).le
    have hl : (t^n*Real.exp (-(5/4*t)))*Real.exp (-((d-5/4)*t))*Real.exp (-(19/20)*t) =
        t^n*Real.exp (-B*t) := by
      rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
      congr 2
      rw [hc]
      ring
    have hr : ((5/4 : ℝ)*8^n*Real.exp (-10))*Real.exp (-(8*(d-5/4)))*Real.exp (-(19/20)*t) =
        ((5/4 : ℝ)*8^n*Real.exp (-(8*d)))*Real.exp (-(19/20)*t) := by
      rw [mul_assoc ((5/4 : ℝ)*8^n), ← Real.exp_add]
      congr 3
      ring
    rw [hl, hr] at hm'
    exact hm'
  have hm := mul_le_mul_of_nonneg_left thetaCuspDeepTailMoment_calibration
    (show 0 ≤ (5/4 : ℝ)*8^n*Real.exp (-(8*d)) by positivity)
  change thetaCuspDeepTailMoment B n ≤ _
  unfold thetaCuspDeepTailErrorScale
  dsimp [d] at hmass hm
  simp only [neg_mul] at hmass hm ⊢
  nlinarith only [hmass, hm]

end
end RHTower
