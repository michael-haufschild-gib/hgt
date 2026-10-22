import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodScaleLocalTailCooling
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSixthSourceUpperOrientation

/-!
# Scale-local fourth/sixth Bell cooling at scale 175/48

Support-gap cooling still proves `1596p < 1` at `A ≥ 175/48`. This retains more than
`989/1000` of the ordinary fourth score and bounds the logarithmic sixth score by
`1003/1000` of its ordinary one-particle score.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Elementary exponential input for the scale-`175/48` cooling step. -/
theorem exp_neg_threeHalves_lt_oneFourth :
    Real.exp (-(3 / 2 : ℝ)) < (1 / 4 : ℝ) := by
  have hone : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) 2
  have hhalf : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at he ⊢
    exact he
  have hlarge : (4 : ℝ) < Real.exp (3 / 2) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos (1 : ℝ), Real.exp_pos (1 / 2 : ℝ)]
  have hprod : Real.exp (-(3 / 2 : ℝ)) * Real.exp (3 / 2) = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (-(3 / 2 : ℝ))]

/-- Above scale `175/48`, normalized higher-tail probability is below `1/1596`. -/
theorem oneThousandFiveHundredNinetySix_mul_thetaCuspLikelihoodTailProbability_lt_one_of_175Over48_le
    {x : ℝ} (hx : 0 ≤ x)
    (hA : (175 / 48 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    1596 * thetaCuspLikelihoodTailProbability (thetaCuspLikelihoodCoordinate x) < 1 := by
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
  have hdelta : 3 / 2 < 3 * (B - B₀) := by
    rw [hBA, hB₀eq]
    dsimp only [A] at hA ⊢
    nlinarith [Real.pi_lt_d4]
  have hB₀B : B₀ ≤ B := by linarith
  have hcompare :=
    thetaCuspHigherLikelihoodSpectralMoment_zero_le_exp_support_comparison hB₀ hB hB₀B
  rw [thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB,
    thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB₀] at hcompare
  have hexp : Real.exp (-3 * (B - B₀)) < (1 / 4 : ℝ) := by
    exact (Real.exp_lt_exp.mpr (by linarith)).trans exp_neg_threeHalves_lt_oneFourth
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
  have hrSmall : 1596 * r < 1 := by
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
  have hpSmall : 1596 * p < 1 := by nlinarith
  simpa only [p, B] using hpSmall

set_option maxHeartbeats 3000000 in
/-- Scale-local Bell losses consume less than eleven thousandths of the ordinary fourth score. -/
theorem nineHundredEightyNineThousandths_mul_ordinaryJetFour_lt_logJetFour_of_175Over48_le
    {x : ℝ} (hx : 0 ≤ x)
    (hScale : (175 / 48 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (989 / 1000 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetFour x <
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
  have hpSmall : 1596 * p < 1 := by
    simpa only [B, p] using
      oneThousandFiveHundredNinetySix_mul_thetaCuspLikelihoodTailProbability_lt_one_of_175Over48_le
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
  have hcoeff : (35 / 2 : ℝ) * p + 15 * p ^ (3 : ℕ) < 11 / 1000 := by
    have hpUpper : p < (1 / 1596 : ℝ) := by linarith
    have hp3 : p ^ (3 : ℕ) < (1 / 1596 : ℝ) ^ (3 : ℕ) :=
      pow_lt_pow_left₀ hpUpper hp.le (by norm_num)
    have hlinear : (35 / 2 : ℝ) * p < 35 / 3192 := by
      have h := mul_lt_mul_of_pos_left hpUpper (by norm_num : (0 : ℝ) < 35 / 2)
      norm_num at h ⊢
      exact h
    have hcubic : 15 * p ^ (3 : ℕ) < (15 / 4065356736 : ℝ) := by
      have h := mul_lt_mul_of_pos_left hp3 (by norm_num : (0 : ℝ) < 15)
      norm_num at h ⊢
      exact h
    calc
      (35 / 2 : ℝ) * p + 15 * p ^ (3 : ℕ) < 35 / 3192 + 15 / 4065356736 :=
        add_lt_add hlinear hcubic
      _ < 11 / 1000 := by norm_num
  have hloss :
      4 * b1 * b3 + 3 * b2 ^ (2 : ℕ) + 6 * b1 ^ (4 : ℕ) < (11 / 1000 : ℝ) * b4 := by
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
  linarith only [hloss, hpositive]


set_option maxHeartbeats 3000000 in

theorem thetaCuspLikelihoodSourceLogPartitionJetSix_lt_oneThousandThreeThousandths_ordinary_of_175Over48_le
    {x : ℝ} (hx : 0 ≤ x)
    (hScale : (175 / 48 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspLikelihoodSourceLogPartitionJetSix x <
      (1003 / 1000 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetSix x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let p := thetaCuspLikelihoodTailProbability B
  let e1 := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  let e4 := thetaCuspLikelihoodNormalizedMoment B 4
  let e5 := thetaCuspLikelihoodNormalizedMoment B 5
  let e6 := thetaCuspLikelihoodNormalizedMoment B 6
  let b1 := 2 * A * e1
  let b2 := 4 * (A ^ (2 : ℕ) * e2 - A * e1)
  let b3 := 8 * (A ^ (3 : ℕ) * e3 - 3 * A ^ (2 : ℕ) * e2 + A * e1)
  let b4 := 16 * (A ^ (4 : ℕ) * e4 - 6 * A ^ (3 : ℕ) * e3 +
    7 * A ^ (2 : ℕ) * e2 - A * e1)
  let b5 := 32 * (A ^ (5 : ℕ) * e5 - 10 * A ^ (4 : ℕ) * e4 +
    25 * A ^ (3 : ℕ) * e3 - 15 * A ^ (2 : ℕ) * e2 + A * e1)
  let b6 := 64 * (A ^ (6 : ℕ) * e6 - 15 * A ^ (5 : ℕ) * e5 +
    65 * A ^ (4 : ℕ) * e4 - 90 * A ^ (3 : ℕ) * e3 +
    31 * A ^ (2 : ℕ) * e2 - A * e1)
  let q2 := 6 * b1 * b5 + 15 * b2 * b4 + 10 * b3 ^ (2 : ℕ)
  let q3 := 15 * b1 ^ (2 : ℕ) * b4 + 60 * b1 * b2 * b3 + 15 * b2 ^ (3 : ℕ)
  let q4 := 20 * b1 ^ (3 : ℕ) * b3 + 45 * b1 ^ (2 : ℕ) * b2 ^ (2 : ℕ)
  let q5 := 15 * b1 ^ (4 : ℕ) * b2
  let q6 := b1 ^ (6 : ℕ)
  have hB : 0 < B := by
    simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hA : 3 < A := by
    simpa only [A] using
      three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx
  have hA0 : 0 < A := by linarith
  have he1 : 0 < e1 := by
    simpa only [e1] using thetaCuspLikelihoodMean_pos hB
  have he2 : 0 < e2 := by
    simpa only [e2] using thetaCuspLikelihoodNormalizedMoment_two_pos hB
  have he12 : 3 * e1 ≤ e2 := by
    have h := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 1
    simpa only [thetaCuspLikelihoodNormalizedMoment_one_eq_mean, e1, e2] using h
  have he23 : 3 * e2 ≤ e3 := by
    simpa only [e2, e3] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
  have he34 : 3 * e3 ≤ e4 := by
    simpa only [e3, e4] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 3
  have he45 : 3 * e4 ≤ e5 := by
    simpa only [e4, e5] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 4
  have he56 : 3 * e5 ≤ e6 := by
    simpa only [e5, e6] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 5
  have he3 : 0 < e3 := lt_of_lt_of_le (mul_pos (by norm_num) he2) he23
  have he4 : 0 < e4 := lt_of_lt_of_le (mul_pos (by norm_num) he3) he34
  have he5 : 0 < e5 := lt_of_lt_of_le (mul_pos (by norm_num) he4) he45
  have he6 : 0 < e6 := lt_of_lt_of_le (mul_pos (by norm_num) he5) he56
  have hpSmall : 1596 * p < 1 := by
    simpa only [B, p] using
      oneThousandFiveHundredNinetySix_mul_thetaCuspLikelihoodTailProbability_lt_one_of_175Over48_le hx hScale
  have h22 : e2 ^ (2 : ℕ) ≤ p * e4 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 2 2
    simpa only [B, p, e2, e4, show 2 + 2 = 4 by norm_num, pow_two] using h
  have hp : 0 < p := by nlinarith [sq_pos_of_pos he2]
  have hp0 : 0 ≤ p := hp.le
  have h11 : e1 ^ (2 : ℕ) ≤ p * e2 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 1 1
    simpa only [B, p, e1, e2, thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 1 = 2 by norm_num, pow_two] using h
  have h12 : e1 * e2 ≤ p * e3 := by
    simpa only [B, p, e1, e2, e3,
      thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 2 = 3 by norm_num] using
        thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 1 2
  have h24 : e2 * e4 ≤ p * e6 := by
    simpa only [B, p, e2, e4, e6, show 2 + 4 = 6 by norm_num] using
      thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 2 4
  have h33 : e3 ^ (2 : ℕ) ≤ p * e6 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 3 3
    simpa only [B, p, e3, e6, show 3 + 3 = 6 by norm_num, pow_two] using h
  have he114 : e1 ^ (2 : ℕ) * e4 ≤ p ^ (2 : ℕ) * e6 := by
    calc
      e1 ^ (2 : ℕ) * e4 ≤ (p * e2) * e4 :=
        mul_le_mul_of_nonneg_right h11 he4.le
      _ = p * (e2 * e4) := by ring
      _ ≤ p * (p * e6) := mul_le_mul_of_nonneg_left h24 hp0
      _ = p ^ (2 : ℕ) * e6 := by ring
  have he123 : e1 * e2 * e3 ≤ p ^ (2 : ℕ) * e6 := by
    calc
      e1 * e2 * e3 ≤ (p * e3) * e3 :=
        mul_le_mul_of_nonneg_right h12 he3.le
      _ = p * e3 ^ (2 : ℕ) := by ring
      _ ≤ p * (p * e6) := mul_le_mul_of_nonneg_left h33 hp0
      _ = p ^ (2 : ℕ) * e6 := by ring
  have he23cube : e2 ^ (3 : ℕ) ≤ p ^ (2 : ℕ) * e6 := by
    calc
      e2 ^ (3 : ℕ) = e2 * e2 ^ (2 : ℕ) := by ring
      _ ≤ e2 * (p * e4) := mul_le_mul_of_nonneg_left h22 he2.le
      _ = p * (e2 * e4) := by ring
      _ ≤ p * (p * e6) := mul_le_mul_of_nonneg_left h24 hp0
      _ = p ^ (2 : ℕ) * e6 := by ring
  have he112 : e1 ^ (4 : ℕ) * e2 ≤ p ^ (4 : ℕ) * e6 := by
    calc
      e1 ^ (4 : ℕ) * e2 = (e1 ^ (2 : ℕ)) ^ (2 : ℕ) * e2 := by ring
      _ ≤ (p * e2) ^ (2 : ℕ) * e2 := by
        gcongr
      _ = p ^ (2 : ℕ) * e2 ^ (3 : ℕ) := by ring
      _ ≤ p ^ (2 : ℕ) * (p ^ (2 : ℕ) * e6) :=
        mul_le_mul_of_nonneg_left he23cube (sq_nonneg p)
      _ = p ^ (4 : ℕ) * e6 := by ring
  have hAe2 : e1 < A * e2 := by
    have hmul := mul_lt_mul_of_pos_right hA he2
    nlinarith
  have hAe3 : 3 * e2 < A * e3 := by
    have hmul := mul_lt_mul_of_pos_right hA he3
    nlinarith
  have hAe4 : 6 * e3 < A * e4 := by
    have hmul := mul_lt_mul_of_pos_right hA he4
    nlinarith
  have hb1 : 0 < b1 := by dsimp only [b1]; positivity
  have hb1Upper : b1 ≤ 2 * A * e1 := by rfl
  have hb2 : 0 < b2 := by
    have hmul := mul_lt_mul_of_pos_left hAe2 hA0
    dsimp only [b2]
    nlinarith [mul_pos hA0 he1]
  have hb2Upper : b2 ≤ 4 * A ^ (2 : ℕ) * e2 := by
    dsimp only [b2]
    nlinarith [mul_pos hA0 he1]
  have hb3 : 0 < b3 := by
    have hmul := mul_lt_mul_of_pos_left hAe3 (pow_pos hA0 2)
    dsimp only [b3]
    nlinarith [mul_pos hA0 he1]
  have hb3Upper : b3 ≤ 8 * A ^ (3 : ℕ) * e3 := by
    have hmul := mul_lt_mul_of_pos_left hAe2 hA0
    dsimp only [b3]
    nlinarith
  have hb4 : 0 < b4 := by
    have hmul := mul_lt_mul_of_pos_left hAe4 (pow_pos hA0 3)
    have htail : A * e1 < 7 * A ^ (2 : ℕ) * e2 := by
      have h := mul_lt_mul_of_pos_left hAe2 hA0
      nlinarith
    dsimp only [b4]
    nlinarith
  have hseven : 7 * e2 ≤ 6 * A * e3 := by
    have hAe3' : 3 * e3 < A * e3 := by
      exact mul_lt_mul_of_pos_right hA he3
    nlinarith
  have hsevenScaled := mul_le_mul_of_nonneg_left hseven (sq_nonneg A)
  have hb4Upper : b4 ≤ 16 * A ^ (4 : ℕ) * e4 := by
    dsimp only [b4]
    nlinarith [mul_pos hA0 he1]
  have hb5Lower : (32 / 6 : ℝ) * A ^ (5 : ℕ) * e5 ≤ b5 := by
    have h := one_sixth_mul_likelihoodSourceLinearFive_le hx
    dsimp only [A, B, e1, e2, e3, e4, e5, b5] at h ⊢
    nlinarith
  have hb5 : 0 < b5 := by
    exact lt_of_lt_of_le (by positivity :
      0 < (32 / 6 : ℝ) * A ^ (5 : ℕ) * e5) hb5Lower
  have hb6Lower : (64 / 30 : ℝ) * A ^ (6 : ℕ) * e6 ≤ b6 := by
    have h := one_thirtieth_mul_likelihoodSourceLinearSix_le hx
    dsimp only [A, B, e1, e2, e3, e4, e5, e6, b6] at h ⊢
    nlinarith
  have hb6 : 0 < b6 := by
    exact lt_of_lt_of_le (by positivity :
      0 < (64 / 30 : ℝ) * A ^ (6 : ℕ) * e6) hb6Lower
  have hb1SqB4 : b1 ^ (2 : ℕ) * b4 ≤ 64 * A ^ (6 : ℕ) * (e1 ^ (2 : ℕ) * e4) := by
    calc
      b1 ^ (2 : ℕ) * b4 ≤ (2 * A * e1) ^ (2 : ℕ) * (16 * A ^ (4 : ℕ) * e4) := by gcongr
      _ = 64 * A ^ (6 : ℕ) * (e1 ^ (2 : ℕ) * e4) := by ring
  have hb1B2B3 : b1 * b2 * b3 ≤ 64 * A ^ (6 : ℕ) * (e1 * e2 * e3) := by
    calc
      b1 * b2 * b3 ≤ (2 * A * e1) * (4 * A ^ (2 : ℕ) * e2) *
          (8 * A ^ (3 : ℕ) * e3) := by gcongr
      _ = 64 * A ^ (6 : ℕ) * (e1 * e2 * e3) := by ring
  have hb2Cube : b2 ^ (3 : ℕ) ≤ 64 * A ^ (6 : ℕ) * e2 ^ (3 : ℕ) := by
    calc
      b2 ^ (3 : ℕ) ≤ (4 * A ^ (2 : ℕ) * e2) ^ (3 : ℕ) :=
        pow_le_pow_left₀ hb2.le hb2Upper 3
      _ = 64 * A ^ (6 : ℕ) * e2 ^ (3 : ℕ) := by ring
  have hq3 : q3 ≤ 2700 * p ^ (2 : ℕ) * b6 := by
    have hterm1 : 15 * b1 ^ (2 : ℕ) * b4 ≤ 960 * A ^ (6 : ℕ) * p ^ (2 : ℕ) * e6 := by
      have h1 := mul_le_mul_of_nonneg_left hb1SqB4 (by norm_num : (0 : ℝ) ≤ 15)
      have h2 := mul_le_mul_of_nonneg_left he114
        (show 0 ≤ 960 * A ^ (6 : ℕ) by positivity)
      nlinarith
    have hterm2 : 60 * b1 * b2 * b3 ≤ 3840 * A ^ (6 : ℕ) * p ^ (2 : ℕ) * e6 := by
      have h1 := mul_le_mul_of_nonneg_left hb1B2B3 (by norm_num : (0 : ℝ) ≤ 60)
      have h2 := mul_le_mul_of_nonneg_left he123
        (show 0 ≤ 3840 * A ^ (6 : ℕ) by positivity)
      nlinarith
    have hterm3 : 15 * b2 ^ (3 : ℕ) ≤ 960 * A ^ (6 : ℕ) * p ^ (2 : ℕ) * e6 := by
      have h1 := mul_le_mul_of_nonneg_left hb2Cube (by norm_num : (0 : ℝ) ≤ 15)
      have h2 := mul_le_mul_of_nonneg_left he23cube
        (show 0 ≤ 960 * A ^ (6 : ℕ) by positivity)
      nlinarith
    have hlead := mul_le_mul_of_nonneg_left hb6Lower
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2700) (sq_nonneg p))
    dsimp only [q3]
    nlinarith
  have hb1FourB2 : b1 ^ (4 : ℕ) * b2 ≤ 64 * A ^ (6 : ℕ) * (e1 ^ (4 : ℕ) * e2) := by
    calc
      b1 ^ (4 : ℕ) * b2 ≤ (2 * A * e1) ^ (4 : ℕ) * (4 * A ^ (2 : ℕ) * e2) := by gcongr
      _ = 64 * A ^ (6 : ℕ) * (e1 ^ (4 : ℕ) * e2) := by ring
  have hq5 : q5 ≤ 450 * p ^ (4 : ℕ) * b6 := by
    have hterm : 15 * b1 ^ (4 : ℕ) * b2 ≤ 960 * A ^ (6 : ℕ) * p ^ (4 : ℕ) * e6 := by
      have h1 := mul_le_mul_of_nonneg_left hb1FourB2 (by norm_num : (0 : ℝ) ≤ 15)
      have h2 := mul_le_mul_of_nonneg_left he112
        (show 0 ≤ 960 * A ^ (6 : ℕ) by positivity)
      nlinarith
    have hlead := mul_le_mul_of_nonneg_left hb6Lower
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 450) (pow_nonneg hp0 4))
    dsimp only [q5]
    nlinarith
  have hq2nonneg : 0 ≤ q2 := by dsimp only [q2]; positivity
  have hq4nonneg : 0 ≤ q4 := by dsimp only [q4]; positivity
  have hq6nonneg : 0 ≤ q6 := by dsimp only [q6]; positivity
  have hpLt : p < (1 / 1596 : ℝ) := by nlinarith
  have hp2 : p ^ (2 : ℕ) < (1 / 1596 : ℝ) ^ (2 : ℕ) :=
    pow_lt_pow_left₀ hpLt hp0 (by norm_num)
  have hp4 : p ^ (4 : ℕ) < (1 / 1596 : ℝ) ^ (4 : ℕ) :=
    pow_lt_pow_left₀ hpLt hp0 (by norm_num)
  have hbudget : 1 + 5400 * p ^ (2 : ℕ) + 10800 * p ^ (4 : ℕ) < (1003 / 1000 : ℝ) := by
    norm_num at hp2 hp4 ⊢
    nlinarith
  have hupper : b6 + 2 * q3 + 24 * q5 < (1003 / 1000 : ℝ) * b6 := by
    have hscaled := mul_lt_mul_of_pos_right hbudget hb6
    nlinarith
  have hdecomp :
      thetaCuspLikelihoodSourceLogPartitionJetSix x =
        b6 - q2 + 2 * q3 - 6 * q4 + 24 * q5 - 120 * q6 := by
    dsimp only [b1, b2, b3, b4, b5, b6, q2, q3, q4, q5, q6,
      A, B, e1, e2, e3, e4, e5, e6]
    unfold thetaCuspLikelihoodSourceLogPartitionJetSix
      thetaCuspLikelihoodSixthCumulant thetaCuspLikelihoodFifthCumulant
      thetaCuspLikelihoodFourthCumulant thetaCuspLikelihoodThirdCumulant
    rw [thetaCuspLikelihoodVariance_eq_normalizedMoment_two_sub_mean_sq]
    unfold thetaCuspLikelihoodNormalizedMoment
    ring
  rw [hdecomp]
  change b6 - q2 + 2 * q3 - 6 * q4 + 24 * q5 - 120 * q6 <
    (1003 / 1000 : ℝ) * b6
  linarith only [hupper, hq2nonneg, hq4nonneg, hq6nonneg]


end
end RHTower

