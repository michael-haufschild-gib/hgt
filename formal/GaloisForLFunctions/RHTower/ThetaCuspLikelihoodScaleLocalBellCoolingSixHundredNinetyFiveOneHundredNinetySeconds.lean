import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodBellTailPolynomialEnvelope
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodScaleLocalBellCoolingTwentyNineEighths

/-!
# Scale-local Bell cooling at scale 695/192

The adjacent dyadic chamber admits `1670r < 1`, hence `1670p < 1`. The generic Bell envelopes then retain
`9895/10000` of the ordinary fourth score and limit sixth inflation to `501/500`.
-/

namespace RHTower

noncomputable section

/-- Elementary exponential input for the scale-`695/192` tail comparison. -/
theorem exp_neg_sevenHundredSeventeenFiveHundredths_lt_threeHundredNinetyNineOneThousandSixHundredSeventieths :
    Real.exp (-(717 / 500 : ℝ)) < (399 / 1670 : ℝ) := by
  have hone : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 217 / 500) 6
  have hsmall : (77 / 50 : ℝ) < Real.exp (217 / 500) := by
    have hsum' : (77 / 50 : ℝ) <
        ∑ k ∈ Finset.range 6, (217 / 500 : ℝ) ^ k / k.factorial := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact hsum'.trans_le hsum
  have hlarge : (1670 / 399 : ℝ) < Real.exp (717 / 500) := by
    rw [show (717 / 500 : ℝ) = 1 + 217 / 500 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos (1 : ℝ), Real.exp_pos (217 / 500 : ℝ)]
  have hprod : Real.exp (-(717 / 500 : ℝ)) * Real.exp (717 / 500) = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (-(717 / 500 : ℝ))]

/-- Above scale `695/192`, higher spectral response is below `1/1670`. -/
theorem oneThousandSixHundredSeventy_mul_thetaCuspHigherLikelihoodSpectralResponse_lt_one_of_695Over192_le
    {x : ℝ} (hx : 0 ≤ x)
    (hA : (695 / 192 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    1670 * thetaCuspHigherLikelihoodSpectralResponse (thetaCuspLikelihoodCoordinate x) < 1 := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let B₀ := thetaCuspLikelihoodCoordinate 0
  let r := thetaCuspHigherLikelihoodSpectralResponse B
  let r₀ := thetaCuspHigherLikelihoodSpectralResponse B₀
  have hB : 0 < B := by
    simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hB₀ : 0 < B₀ := by
    simpa only [B₀] using thetaCuspLikelihoodCoordinate_pos (x := 0) (by norm_num)
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hB₀eq : B₀ = Real.pi - 3 / 2 := by
    dsimp [B₀, thetaCuspLikelihoodCoordinate]
    norm_num
  have hdelta : 717 / 500 < 3 * (B - B₀) := by
    rw [hBA, hB₀eq]
    dsimp only [A] at hA ⊢
    nlinarith [Real.pi_lt_d4]
  have hB₀B : B₀ ≤ B := by linarith
  have hcompare :=
    thetaCuspHigherLikelihoodSpectralMoment_zero_le_exp_support_comparison hB₀ hB hB₀B
  rw [thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB,
    thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB₀] at hcompare
  have hexp : Real.exp (-3 * (B - B₀)) < (399 / 1670 : ℝ) :=
    (Real.exp_lt_exp.mpr (by linarith)).trans
      exp_neg_sevenHundredSeventeenFiveHundredths_lt_threeHundredNinetyNineOneThousandSixHundredSeventieths
  have hr₀0 : 0 ≤ r₀ := by
    dsimp only [r₀]
    rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB₀]
    exact thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hcal : 399 * r₀ < 1 := by
    simpa only [r₀, B₀] using
      three_hundred_ninety_nine_mul_thetaCuspHigherLikelihoodSpectralResponse_lt_one
        (x := 0) (by norm_num)
  have hcompare' : r ≤ Real.exp (-3 * (B - B₀)) * r₀ := by
    simpa only [r, r₀] using hcompare
  simpa only [B, r] using (show 1670 * r < 1 by nlinarith)

/-- Above scale `695/192`, normalized higher-tail probability is below `1/1670`. -/
theorem oneThousandSixHundredSeventy_mul_thetaCuspLikelihoodTailProbability_lt_one_of_695Over192_le
    {x : ℝ} (hx : 0 ≤ x)
    (hA : (695 / 192 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    1670 * thetaCuspLikelihoodTailProbability (thetaCuspLikelihoodCoordinate x) < 1 := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let B₀ := thetaCuspLikelihoodCoordinate 0
  let r := thetaCuspHigherLikelihoodSpectralResponse B
  let r₀ := thetaCuspHigherLikelihoodSpectralResponse B₀
  let p := thetaCuspLikelihoodTailProbability B
  have hB : 0 < B := by
    simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hB₀ : 0 < B₀ := by
    simpa only [B₀] using thetaCuspLikelihoodCoordinate_pos (x := 0) (by norm_num)
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hB₀eq : B₀ = Real.pi - 3 / 2 := by
    dsimp [B₀, thetaCuspLikelihoodCoordinate]
    norm_num
  have hdelta : 717 / 500 < 3 * (B - B₀) := by
    rw [hBA, hB₀eq]
    dsimp only [A] at hA ⊢
    nlinarith [Real.pi_lt_d4]
  have hB₀B : B₀ ≤ B := by linarith
  have hcompare :=
    thetaCuspHigherLikelihoodSpectralMoment_zero_le_exp_support_comparison hB₀ hB hB₀B
  rw [thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB,
    thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB₀] at hcompare
  have hexp : Real.exp (-3 * (B - B₀)) < (399 / 1670 : ℝ) :=
    (Real.exp_lt_exp.mpr (by linarith)).trans
      exp_neg_sevenHundredSeventeenFiveHundredths_lt_threeHundredNinetyNineOneThousandSixHundredSeventieths
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
  have hrSmall : 1670 * r < 1 := by
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
  simpa only [p, B] using (show 1670 * p < 1 by nlinarith)

/-- Scale-`695/192` fourth Bell conversion from the local tail certificate. -/
theorem nineThousandEightHundredNinetyFiveTenThousandths_mul_ordinaryJetFour_lt_logJetFour_of_695Over192_le
    {x : ℝ} (hx : 0 ≤ x)
    (hA : (695 / 192 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (9895 / 10000 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetFour x <
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  let p := thetaCuspLikelihoodTailProbability (thetaCuspLikelihoodCoordinate x)
  have hp : 0 < p := by
    simpa only [p] using thetaCuspLikelihoodTailProbability_coordinate_pos hx
  have hpSmall : 1670 * p < 1 := by
    simpa only [p] using
      oneThousandSixHundredSeventy_mul_thetaCuspLikelihoodTailProbability_lt_one_of_695Over192_le
        hx hA
  have hpUpper : p < (1 / 1670 : ℝ) := by linarith
  have hp3 : p ^ (3 : ℕ) < (1 / 1670 : ℝ) ^ (3 : ℕ) :=
    pow_lt_pow_left₀ hpUpper hp.le (by norm_num)
  have hlinear : (35 / 2 : ℝ) * p < 35 / 3340 := by
    have h := mul_lt_mul_of_pos_left hpUpper (by norm_num : (0 : ℝ) < 35 / 2)
    norm_num at h ⊢
    exact h
  have hcubic : 15 * p ^ (3 : ℕ) < (15 / 4657463000 : ℝ) := by
    have h := mul_lt_mul_of_pos_left hp3 (by norm_num : (0 : ℝ) < 15)
    norm_num at h ⊢
    exact h
  have hloss : (35 / 2 : ℝ) * p + 15 * p ^ (3 : ℕ) < 105 / 10000 := by
    calc
      (35 / 2 : ℝ) * p + 15 * p ^ (3 : ℕ) < 35 / 3340 + 15 / 4657463000 :=
        add_lt_add hlinear hcubic
      _ < 105 / 10000 := by norm_num
  have hretention :
      (9895 / 10000 : ℝ) < 1 - ((35 / 2 : ℝ) * p + 15 * p ^ (3 : ℕ)) := by
    linarith
  have hord := thetaCuspLikelihoodSourceOrdinaryJetFour_pos hx
  have hscaled := mul_lt_mul_of_pos_right hretention hord
  have henvelope := tailPolynomial_mul_ordinaryJetFour_lt_sourceLogJetFour hx
  change
    (1 - ((35 / 2 : ℝ) * p + 15 * p ^ (3 : ℕ))) *
        thetaCuspLikelihoodSourceOrdinaryJetFour x <
      thetaCuspLikelihoodSourceLogPartitionJetFour x at henvelope
  exact hscaled.trans henvelope

/-- Scale-`695/192` sixth Bell conversion from the local tail certificate. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetSix_lt_fiveHundredOneFiveHundredths_ordinary_of_695Over192_le
    {x : ℝ} (hx : 0 ≤ x)
    (hA : (695 / 192 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspLikelihoodSourceLogPartitionJetSix x <
      (501 / 500 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetSix x := by
  let p := thetaCuspLikelihoodTailProbability (thetaCuspLikelihoodCoordinate x)
  have hp : 0 < p := by
    simpa only [p] using thetaCuspLikelihoodTailProbability_coordinate_pos hx
  have hpSmall : 1670 * p < 1 := by
    simpa only [p] using
      oneThousandSixHundredSeventy_mul_thetaCuspLikelihoodTailProbability_lt_one_of_695Over192_le
        hx hA
  have hpUpper : p < (1 / 1670 : ℝ) := by nlinarith
  have hp2 : p ^ (2 : ℕ) < (1 / 1670 : ℝ) ^ (2 : ℕ) :=
    pow_lt_pow_left₀ hpUpper hp.le (by norm_num)
  have hp4 : p ^ (4 : ℕ) < (1 / 1670 : ℝ) ^ (4 : ℕ) :=
    pow_lt_pow_left₀ hpUpper hp.le (by norm_num)
  have hbudget : 1 + 5400 * p ^ (2 : ℕ) + 10800 * p ^ (4 : ℕ) < (501 / 500 : ℝ) := by
    norm_num at hp2 hp4 ⊢
    nlinarith
  have hord := thetaCuspLikelihoodSourceOrdinaryJetSix_pos hx
  have hscaled := mul_lt_mul_of_pos_right hbudget hord
  have henvelope := sourceLogJetSix_lt_tailPolynomial_mul_ordinaryJetSix hx
  change thetaCuspLikelihoodSourceLogPartitionJetSix x <
    (1 + 5400 * p ^ (2 : ℕ) + 10800 * p ^ (4 : ℕ)) *
      thetaCuspLikelihoodSourceOrdinaryJetSix x at henvelope
  exact henvelope.trans hscaled

end

end RHTower
