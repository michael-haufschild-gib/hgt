import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodFourthScaleEightyNineTwentyFourthsAffineLower

/-!
# Scale-local cooling of the theta likelihood tail

The spectral support gap `t ≥ 3` makes the zeroth tilted moment contract exponentially when the
likelihood coordinate increases. Transporting the seam calibration to scale `59/16` gives the
new sharp local law `1995p < 1`. In the fourth Bell decomposition this improves retention of the
ordinary fourth score from `19/20` to `99/100`.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- A support gap of three transports zeroth tilted mass with rate three. -/
theorem thetaCuspHigherLikelihoodSpectralMoment_zero_le_exp_support_comparison
    {B₀ B : ℝ} (hB₀ : 0 < B₀) (hB : 0 < B) (hB₀B : B₀ ≤ B) :
    thetaCuspHigherLikelihoodSpectralMoment B 0 ≤
      Real.exp (-3 * (B - B₀)) * thetaCuspHigherLikelihoodSpectralMoment B₀ 0 := by
  rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral,
    thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
  have hleft := integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 0 hB
  have hright :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 0 hB₀).const_mul
      (Real.exp (-3 * (B - B₀)))
  rw [← integral_const_mul]
  apply integral_mono_ae hleft hright
  filter_upwards [ae_three_le_thetaCuspHigherLikelihoodSpectralMeasure] with t ht
  simp only [pow_zero, one_mul]
  have hdelta : 0 ≤ B - B₀ := by linarith
  have hexp : Real.exp (-(B - B₀) * t) ≤ Real.exp (-3 * (B - B₀)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [show -B * t = -B₀ * t + -(B - B₀) * t by ring, Real.exp_add]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hexp (Real.exp_pos (-B₀ * t)).le

/-- Rational exponential comparison used by scale-local cooling. -/
theorem exp_neg_thirteenEighths_lt_oneFifth :
    Real.exp (-(13 / 8 : ℝ)) < (1 / 5 : ℝ) := by
  have hone : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 8) 4
  have hfiveEighths : (93 / 50 : ℝ) ≤ Real.exp (5 / 8) := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at he ⊢
    exact (by norm_num : (93 / 50 : ℝ) ≤ 5717 / 3072).trans he
  have hlarge : (5 : ℝ) < Real.exp (13 / 8) := by
    rw [show (13 / 8 : ℝ) = 1 + 5 / 8 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos (1 : ℝ), Real.exp_pos (5 / 8 : ℝ)]
  have hprod : Real.exp (-(13 / 8 : ℝ)) * Real.exp (13 / 8 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (-(13 / 8 : ℝ))]

/-- Above scale `59/16`, normalized higher-tail probability is below `1/1995`. -/
theorem oneThousandNineHundredNinetyFive_mul_thetaCuspLikelihoodTailProbability_lt_one_of_59Over16_le
    {x : ℝ} (hx : 0 ≤ x)
    (hA : (59 / 16 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    1995 * thetaCuspLikelihoodTailProbability (thetaCuspLikelihoodCoordinate x) < 1 := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let B₀ := thetaCuspLikelihoodCoordinate 0
  let r := thetaCuspHigherLikelihoodSpectralResponse B
  let r₀ := thetaCuspHigherLikelihoodSpectralResponse B₀
  let p := thetaCuspLikelihoodTailProbability B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hB₀ : 0 < B₀ := by
    simpa only [B₀] using thetaCuspLikelihoodCoordinate_pos (x := 0) (by norm_num)
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hB₀eq : B₀ = Real.pi - 3 / 2 := by
    dsimp [B₀, thetaCuspLikelihoodCoordinate]
    norm_num
  have hdelta : 13 / 8 < 3 * (B - B₀) := by
    rw [hBA, hB₀eq]
    dsimp only [A] at hA ⊢
    nlinarith [Real.pi_lt_d4]
  have hB₀B : B₀ ≤ B := by linarith
  have hcompare :=
    thetaCuspHigherLikelihoodSpectralMoment_zero_le_exp_support_comparison hB₀ hB hB₀B
  rw [thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB,
    thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB₀] at hcompare
  have hexp : Real.exp (-3 * (B - B₀)) < (1 / 5 : ℝ) := by
    exact (Real.exp_lt_exp.mpr (by linarith)).trans exp_neg_thirteenEighths_lt_oneFifth
  have hr₀0 : 0 ≤ r₀ := by
    dsimp only [r₀]
    rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB₀]
    exact thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
    exact thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hcal : 399 * r₀ < 1 := by
    simpa only [r₀, B₀] using
      three_hundred_ninety_nine_mul_thetaCuspHigherLikelihoodSpectralResponse_lt_one
        (x := 0) (by norm_num)
  have hrSmall : 1995 * r < 1 := by
    have hcompare' : r ≤ Real.exp (-3 * (B - B₀)) * r₀ := by
      simpa only [r, r₀] using hcompare
    nlinarith
  have hpEq : p = r / (1 + r) := by
    dsimp only [p, r]
    unfold thetaCuspLikelihoodTailProbability thetaCuspLikelihoodNormalizedMoment
      thetaCuspLikelihoodPartition
    rw [thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
  have hden : 0 < 1 + r := by linarith
  have hpr : p ≤ r := by
    rw [hpEq]
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg r]
  have hpSmall : 1995 * p < 1 := by nlinarith
  simpa only [p, B] using hpSmall

set_option maxHeartbeats 3000000 in
/-- Scale-local Bell losses consume less than one hundredth of the ordinary fourth score. -/
theorem ninetyNineHundredths_mul_ordinaryJetFour_lt_logJetFour_of_59Over16_le
    {x : ℝ} (hx : 0 ≤ x)
    (hScale : (59 / 16 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (99 / 100 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetFour x <
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let p := thetaCuspLikelihoodTailProbability B
  let e1 := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  let e4 := thetaCuspLikelihoodNormalizedMoment B 4
  let b1 := 2 * A * e1
  let b2 := 4 * (A ^ (2 : ℕ) * e2 - A * e1)
  let b3 := 8 * (A ^ (3 : ℕ) * e3 - 3 * A ^ (2 : ℕ) * e2 + A * e1)
  let b4 := thetaCuspLikelihoodSourceOrdinaryJetFour x
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hA : 3 < A := by
    simpa only [A] using three_lt_thetaCuspSingleAtomReflectionScale
      (n := 1) (by norm_num) hx
  have hA0 : 0 < A := by linarith
  have he1 : 0 < e1 := by simpa only [e1] using thetaCuspLikelihoodMean_pos hB
  have he2 : 0 < e2 := by
    simpa only [e2] using thetaCuspLikelihoodNormalizedMoment_two_pos hB
  have he12 : 3 * e1 ≤ e2 := by
    simpa only [e1, e2, thetaCuspLikelihoodNormalizedMoment_one_eq_mean] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 1
  have he23 : 3 * e2 ≤ e3 := by
    simpa only [e2, e3] using three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
  have he34 : 3 * e3 ≤ e4 := by
    simpa only [e3, e4] using three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 3
  have he3 : 0 < e3 := lt_of_lt_of_le (mul_pos (by norm_num) he2) he23
  have he4 : 0 < e4 := lt_of_lt_of_le (mul_pos (by norm_num) he3) he34
  have hpSmall : 1995 * p < 1 := by
    simpa only [B, p] using
      oneThousandNineHundredNinetyFive_mul_thetaCuspLikelihoodTailProbability_lt_one_of_59Over16_le
        hx hScale
  have hp : 0 < p := by
    have h22 := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 2 2
    have h22' : e2 ^ (2 : ℕ) ≤ p * e4 := by
      simpa only [B, p, e2, e4, show 2 + 2 = 4 by norm_num, pow_two] using h22
    nlinarith [sq_pos_of_pos he2]
  have h11 : e1 ^ (2 : ℕ) ≤ p * e2 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 1 1
    simpa only [B, p, e1, e2, thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 1 = 2 by norm_num, pow_two] using h
  have h13 : e1 * e3 ≤ p * e4 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 1 3
    simpa only [B, p, e1, e3, e4, thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 3 = 4 by norm_num] using h
  have h22 : e2 ^ (2 : ℕ) ≤ p * e4 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 2 2
    simpa only [B, p, e2, e4, show 2 + 2 = 4 by norm_num, pow_two] using h
  have hb1 : 0 < b1 := by dsimp only [b1]; positivity
  have hAe2 : e1 < A * e2 := by
    have hmul := mul_lt_mul_of_pos_right hA he2
    nlinarith
  have hb2 : 0 < b2 := by
    have hmul := mul_lt_mul_of_pos_left hAe2 hA0
    dsimp only [b2]
    nlinarith
  have hb2Upper : b2 ≤ 4 * A ^ (2 : ℕ) * e2 := by
    dsimp only [b2]
    nlinarith [mul_pos hA0 he1]
  have hAe3 : 3 * e2 < A * e3 := by
    have hmul := mul_lt_mul_of_pos_right hA he3
    nlinarith
  have hb3 : 0 < b3 := by
    have hmul := mul_lt_mul_of_pos_left hAe3 (pow_pos hA0 2)
    dsimp only [b3]
    nlinarith [mul_pos hA0 he1]
  have hb3Upper : b3 ≤ 8 * A ^ (3 : ℕ) * e3 := by
    dsimp only [b3]
    have hcross : A * e1 ≤ 3 * A ^ (2 : ℕ) * e2 := by
      have hleft : A * e1 ≤ A * (e2 / 3) := by
        apply mul_le_mul_of_nonneg_left (by linarith) hA0.le
      have hright : A * (e2 / 3) ≤ 3 * A ^ (2 : ℕ) * e2 := by
        nlinarith [mul_pos hA0 he2]
      exact hleft.trans hright
    nlinarith
  have hb4Lower : (32 / 5 : ℝ) * A ^ (4 : ℕ) * e4 ≤ b4 := by
    simpa only [A, B, e4, b4] using two_fifths_le_thetaCuspLikelihoodSourceOrdinaryJetFour hx
  have hb4 : 0 < b4 := lt_of_lt_of_le (by positivity) hb4Lower
  have hb1b3Core : b1 * b3 ≤ 16 * A ^ (4 : ℕ) * (e1 * e3) := by
    calc
      b1 * b3 ≤ (2 * A * e1) * (8 * A ^ (3 : ℕ) * e3) := by
        dsimp only [b1]
        gcongr
      _ = 16 * A ^ (4 : ℕ) * (e1 * e3) := by ring
  have hb1b3Moment : 16 * A ^ (4 : ℕ) * (e1 * e3) ≤ 16 * A ^ (4 : ℕ) * (p * e4) := by
    gcongr
  have hb1b3 : 4 * b1 * b3 ≤ 10 * p * b4 := by
    have hcore := hb1b3Core.trans hb1b3Moment
    have hscaled := mul_le_mul_of_nonneg_left hb4Lower (by positivity : 0 ≤ 10 * p)
    nlinarith
  have hb2sqCore : b2 ^ (2 : ℕ) ≤ 16 * A ^ (4 : ℕ) * e2 ^ (2 : ℕ) := by
    have hupper0 : 0 ≤ 4 * A ^ (2 : ℕ) * e2 := by positivity
    have hpow := pow_le_pow_left₀ hb2.le hb2Upper 2
    calc
      b2 ^ (2 : ℕ) ≤ (4 * A ^ (2 : ℕ) * e2) ^ (2 : ℕ) := hpow
      _ = 16 * A ^ (4 : ℕ) * e2 ^ (2 : ℕ) := by ring
  have hb2sqMoment : 16 * A ^ (4 : ℕ) * e2 ^ (2 : ℕ) ≤ 16 * A ^ (4 : ℕ) * (p * e4) := by
    gcongr
  have hb2sq : 3 * b2 ^ (2 : ℕ) ≤ (15 / 2 : ℝ) * p * b4 := by
    have hcore := hb2sqCore.trans hb2sqMoment
    have hscaled := mul_le_mul_of_nonneg_left hb4Lower
      (by positivity : 0 ≤ (15 / 2 : ℝ) * p)
    nlinarith
  have he1four : e1 ^ (4 : ℕ) ≤ p ^ (3 : ℕ) * e4 := by
    have h11sq := pow_le_pow_left₀ (sq_nonneg e1) h11 2
    have hp0 : 0 ≤ p := hp.le
    have hstep : (p * e2) ^ (2 : ℕ) ≤ p ^ (2 : ℕ) * (p * e4) := by
      rw [mul_pow]
      gcongr
    calc
      e1 ^ (4 : ℕ) = (e1 ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ ≤ (p * e2) ^ (2 : ℕ) := h11sq
      _ ≤ p ^ (2 : ℕ) * (p * e4) := hstep
      _ = p ^ (3 : ℕ) * e4 := by ring
  have hb1four : 6 * b1 ^ (4 : ℕ) ≤ 15 * p ^ (3 : ℕ) * b4 := by
    have hcore : 6 * b1 ^ (4 : ℕ) ≤ 96 * A ^ (4 : ℕ) * (p ^ (3 : ℕ) * e4) := by
      dsimp only [b1]
      have hscaled := mul_le_mul_of_nonneg_left he1four
        (by positivity : 0 ≤ 96 * A ^ (4 : ℕ))
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hb4Lower
      (by positivity : 0 ≤ 15 * p ^ (3 : ℕ))
    nlinarith
  have hcoeff : (35 / 2 : ℝ) * p + 15 * p ^ (3 : ℕ) < 1 / 100 := by
    have hpUpper : p < (1 / 1995 : ℝ) := by linarith
    have hp3 : p ^ (3 : ℕ) < (1 / 1995 : ℝ) ^ (3 : ℕ) :=
      pow_lt_pow_left₀ hpUpper hp.le (by norm_num)
    have hlinear : (35 / 2 : ℝ) * p < 35 / 3990 := by
      have h := mul_lt_mul_of_pos_left hpUpper (by norm_num : (0 : ℝ) < 35 / 2)
      norm_num at h ⊢
      exact h
    have hcubic : 15 * p ^ (3 : ℕ) < (15 / 7940149875 : ℝ) := by
      have h := mul_lt_mul_of_pos_left hp3 (by norm_num : (0 : ℝ) < 15)
      norm_num at h ⊢
      exact h
    calc
      (35 / 2 : ℝ) * p + 15 * p ^ (3 : ℕ) < 35 / 3990 + 15 / 7940149875 :=
        add_lt_add hlinear hcubic
      _ < 1 / 100 := by norm_num
  have hloss :
      4 * b1 * b3 + 3 * b2 ^ (2 : ℕ) + 6 * b1 ^ (4 : ℕ) < (1 / 100 : ℝ) * b4 := by
    have hsum :
        4 * b1 * b3 + 3 * b2 ^ (2 : ℕ) + 6 * b1 ^ (4 : ℕ) ≤
          ((35 / 2 : ℝ) * p + 15 * p ^ (3 : ℕ)) * b4 := by
      calc
        4 * b1 * b3 + 3 * b2 ^ (2 : ℕ) + 6 * b1 ^ (4 : ℕ) ≤
            10 * p * b4 + (15 / 2 : ℝ) * p * b4 + 15 * p ^ (3 : ℕ) * b4 :=
          add_le_add (add_le_add hb1b3 hb2sq) hb1four
        _ = ((35 / 2 : ℝ) * p + 15 * p ^ (3 : ℕ)) * b4 := by ring
    exact lt_of_le_of_lt hsum (mul_lt_mul_of_pos_right hcoeff hb4)
  have hdecomp :
      thetaCuspLikelihoodSourceLogPartitionJetFour x =
        b4 - 4 * b1 * b3 - 3 * b2 ^ (2 : ℕ) + 12 * b1 ^ (2 : ℕ) * b2 - 6 * b1 ^ (4 : ℕ) := by
    dsimp only [b1, b2, b3, b4, A, B, e1, e2, e3, e4]
    unfold thetaCuspLikelihoodSourceOrdinaryJetFour
      thetaCuspLikelihoodSourceLogPartitionJetFour thetaCuspLikelihoodFourthCumulant
      thetaCuspLikelihoodThirdCumulant
    rw [thetaCuspLikelihoodVariance_eq_normalizedMoment_two_sub_mean_sq]
    unfold thetaCuspLikelihoodNormalizedMoment thetaCuspLikelihoodMean
    ring
  rw [hdecomp]
  have hpositive : 0 < 12 * b1 ^ (2 : ℕ) * b2 := by positivity
  nlinarith

end
end RHTower
