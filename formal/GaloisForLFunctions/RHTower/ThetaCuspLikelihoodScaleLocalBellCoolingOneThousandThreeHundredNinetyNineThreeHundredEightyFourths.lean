import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodBellTailPolynomialEnvelope
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodScaleLocalBellCoolingOneHundredSeventyFiveFortyEighths

/-!
# Scale-local Bell cooling at scale 1399/384

The support-gap comparison remains beyond `3/2`, so the literal tail certificate `1596p < 1`
survives on the next inward chamber.  The scale-free Bell compiler then supplies both fourth and
sixth logarithmic conversion factors without repeating their moment algebra.
-/

namespace RHTower

noncomputable section

/-- Above scale `1399/384`, normalized higher-tail probability is below `1/1596`. -/
theorem oneThousandFiveHundredNinetySix_mul_thetaCuspLikelihoodTailProbability_lt_one_of_1399Over384_le
    {x : ℝ} (hx : 0 ≤ x)
    (hA : (1399 / 384 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    1596 * thetaCuspLikelihoodTailProbability (thetaCuspLikelihoodCoordinate x) < 1 := by
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
  have hdelta : 3 / 2 < 3 * (B - B₀) := by
    rw [hBA, hB₀eq]
    dsimp only [A] at hA ⊢
    nlinarith [Real.pi_lt_d4]
  have hB₀B : B₀ ≤ B := by linarith
  have hcompare :=
    thetaCuspHigherLikelihoodSpectralMoment_zero_le_exp_support_comparison hB₀ hB hB₀B
  rw [thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB,
    thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB₀] at hcompare
  have hexp : Real.exp (-3 * (B - B₀)) < (1 / 4 : ℝ) :=
    (Real.exp_lt_exp.mpr (by linarith)).trans exp_neg_threeHalves_lt_oneFourth
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
  simpa only [p, B] using (show 1596 * p < 1 by nlinarith)

/-- Scale-`1399/384` fourth Bell conversion, compiled from the scalar tail certificate. -/
theorem nineHundredEightyNineThousandths_mul_ordinaryJetFour_lt_logJetFour_of_1399Over384_le
    {x : ℝ} (hx : 0 ≤ x)
    (hA : (1399 / 384 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (989 / 1000 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetFour x <
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  exact nineHundredEightyNineThousandths_mul_ordinaryJetFour_lt_sourceLogJetFour_of_tail
    hx (oneThousandFiveHundredNinetySix_mul_thetaCuspLikelihoodTailProbability_lt_one_of_1399Over384_le
      hx hA)

/-- Scale-`1399/384` sixth Bell conversion, compiled from the same scalar tail certificate. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetSix_lt_oneThousandThreeThousandths_ordinary_of_1399Over384_le
    {x : ℝ} (hx : 0 ≤ x)
    (hA : (1399 / 384 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspLikelihoodSourceLogPartitionJetSix x <
      (1003 / 1000 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetSix x := by
  exact sourceLogJetSix_lt_oneThousandThreeThousandths_ordinary_of_tail
    hx (oneThousandFiveHundredNinetySix_mul_thetaCuspLikelihoodTailProbability_lt_one_of_1399Over384_le
      hx hA)

end

end RHTower
