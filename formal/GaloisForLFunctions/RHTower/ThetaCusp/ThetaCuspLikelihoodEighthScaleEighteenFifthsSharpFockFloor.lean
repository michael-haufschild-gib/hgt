import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodEighthDominantSingleCoreSharp
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSixthEighthScaleSevenHalvesCoupling
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodScaleLocalBellCoolingEighteenFifths

/-!
# Sharp scale-18/5 eighth Fock floor

At `A ≥ 18/5`, the exact one-particle core exceeds `10575 A^(8 : ℕ)`, while `59/20` dominant
pairs fit inside one dominant single.  Complete non-dominant-pair and higher-even losses leave
`6368` exponential units.  The local `1560p<1` normalization gives the literal logarithmic
floor `1629162 A^(8 : ℕ) exp(-3A) < J₈`.
-/

namespace RHTower

noncomputable section

/-- Scale-local exact algebraic floor for the dominant one-particle core. -/
theorem tenThousandFiveHundredSeventyFive_mul_pow_eight_lt_thetaCuspLikelihoodEighthDominantSingleCore_of_18Over5_le
    {A : ℝ} (hA : (18 / 5 : ℝ) ≤ A) :
    10575 * A ^ (8 : ℕ) < thetaCuspLikelihoodEighthDominantSingleCore A := by
  let B := A - 3 / 2
  have hB : 0 < B := by
    dsimp only [B]
    linarith
  change 10575 * A ^ (8 : ℕ) <
    16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
      18 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (3 * A)
  let s := A - 18 / 5
  have hs : 0 ≤ s := by dsimp only [s]; linarith
  have hmul : 0 < B ^ (9 : ℕ) *
      (16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
        18 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (3 * A) -
        10575 * A ^ (8 : ℕ)) := by
    unfold thetaCuspLikelihoodEighthSourceScoreRayTransform
      thetaCuspLikelihoodEighthSourceScore
      thetaCuspLikelihoodEighthSourceScoreDerivOne
      thetaCuspLikelihoodEighthSourceScoreDerivTwo
      thetaCuspLikelihoodEighthSourceScoreDerivThree
      thetaCuspLikelihoodEighthSourceScoreDerivFour
      thetaCuspLikelihoodEighthSourceScoreDerivFive
      thetaCuspLikelihoodEighthSourceScoreDerivSix
      thetaCuspLikelihoodEighthSourceScoreDerivSeven
      thetaCuspLikelihoodEighthSourceScoreDerivEight
    field_simp [hB.ne']
    dsimp only [B]
    rw [show A = 18 / 5 + s by dsimp only [s]; ring]
    ring_nf
    positivity
  have hdiff : 0 <
      16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
        18 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (3 * A) -
        10575 * A ^ (8 : ℕ) :=
    pos_of_mul_pos_right hmul (pow_nonneg hB.le 9)
  linarith

/-- Restoring the dominant exponential preserves the scale-local core floor. -/
theorem tenThousandFiveHundredSeventyFive_mul_pow_eight_exp_lt_thetaCuspLikelihoodEighthDominantSingleMass_of_18Over5_le
    {A : ℝ} (hA : (18 / 5 : ℝ) ≤ A) :
    10575 * A ^ (8 : ℕ) * Real.exp (-(3 * A)) <
      thetaCuspLikelihoodEighthDominantSingleMass A := by
  have hcore :=
    tenThousandFiveHundredSeventyFive_mul_pow_eight_lt_thetaCuspLikelihoodEighthDominantSingleCore_of_18Over5_le
      hA
  have hscaled := mul_lt_mul_of_pos_left hcore (Real.exp_pos (-(3 * A)))
  unfold thetaCuspLikelihoodEighthDominantSingleMass
  nlinarith

/-- At scale `18/5`, the Taylor certificate absorbs `59/20` dominant pairs. -/
theorem fiftyNineTwentieths_mul_thetaCuspLikelihoodEighthDominantPairCore_lt_taylor_mul_singleCore_of_18Over5_le
    {A : ℝ} (hA : (18 / 5 : ℝ) ≤ A) :
    (59 / 20 : ℝ) * thetaCuspLikelihoodEighthDominantPairCore A <
      thetaCuspLikelihoodEighthDominantTaylorTwenty A *
        thetaCuspLikelihoodEighthDominantSingleCore A := by
  let B := A - 3 / 2
  have hB : 0 < B := by dsimp only [B]; linarith
  change
    (59 / 20 : ℝ) * (256 * thetaCuspLikelihoodEighthSourceScore (6 * A) +
        576 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (6 * A) +
        324 / B ^ (2 : ℕ) *
          thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform (A / B) (6 * A)) <
      thetaCuspLikelihoodEighthDominantTaylorTwenty A *
        (16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
          18 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (3 * A))
  let s := A - 18 / 5
  have hs : 0 ≤ s := by dsimp only [s]; linarith
  have hmul : 0 < B ^ (10 : ℕ) *
      (thetaCuspLikelihoodEighthDominantTaylorTwenty A *
          (16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
            18 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (3 * A)) -
        (59 / 20 : ℝ) * (256 * thetaCuspLikelihoodEighthSourceScore (6 * A) +
          576 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (6 * A) +
          324 / B ^ (2 : ℕ) *
            thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform (A / B) (6 * A))) := by
    unfold thetaCuspLikelihoodEighthDominantTaylorTwenty
      thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform
      thetaCuspLikelihoodEighthSourceScoreRayTransform
      thetaCuspLikelihoodEighthSourceScore
      thetaCuspLikelihoodEighthSourceScoreDerivOne
      thetaCuspLikelihoodEighthSourceScoreDerivTwo
      thetaCuspLikelihoodEighthSourceScoreDerivThree
      thetaCuspLikelihoodEighthSourceScoreDerivFour
      thetaCuspLikelihoodEighthSourceScoreDerivFive
      thetaCuspLikelihoodEighthSourceScoreDerivSix
      thetaCuspLikelihoodEighthSourceScoreDerivSeven
      thetaCuspLikelihoodEighthSourceScoreDerivEight
    norm_num [Finset.sum_range_succ]
    field_simp [hB.ne']
    dsimp only [B]
    rw [show A = 18 / 5 + s by dsimp only [s]; ring]
    ring_nf
    positivity
  have hdiff : 0 <
      thetaCuspLikelihoodEighthDominantTaylorTwenty A *
          (16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
            18 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (3 * A)) -
        (59 / 20 : ℝ) * (256 * thetaCuspLikelihoodEighthSourceScore (6 * A) +
          576 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (6 * A) +
          324 / B ^ (2 : ℕ) *
            thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform (A / B) (6 * A)) :=
    pos_of_mul_pos_right hmul (pow_nonneg hB.le 10)
  linarith

/-- Restoring exponential weights preserves `59/20` dominant-pair absorption. -/
theorem fiftyNineTwentieths_mul_thetaCuspLikelihoodEighthDominantPairMass_lt_singleMass_of_18Over5_le
    {A : ℝ} (hA : (18 / 5 : ℝ) ≤ A) :
    (59 / 20 : ℝ) * thetaCuspLikelihoodEighthDominantPairMass A <
      thetaCuspLikelihoodEighthDominantSingleMass A := by
  have hAseam : (157 / 50 : ℝ) ≤ A := by linarith
  have hcore :=
    fiftyNineTwentieths_mul_thetaCuspLikelihoodEighthDominantPairCore_lt_taylor_mul_singleCore_of_18Over5_le
      hA
  have hsingle : 0 < thetaCuspLikelihoodEighthDominantSingleCore A := by
    simpa only [thetaCuspLikelihoodEighthDominantSingleCore] using
      thetaCuspLikelihoodDominantEighthScoreCore_pos hAseam
  have hexp : Real.exp (-(3 * A)) *
      thetaCuspLikelihoodEighthDominantTaylorTwenty A ≤ 1 := by
    calc
      Real.exp (-(3 * A)) * thetaCuspLikelihoodEighthDominantTaylorTwenty A ≤
          Real.exp (-(3 * A)) * Real.exp (3 * A) := by
        gcongr
        exact thetaCuspLikelihoodEighthDominantTaylorTwenty_le_exp (by linarith)
      _ = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have habsorb : (59 / 20 : ℝ) *
      (Real.exp (-(3 * A)) * thetaCuspLikelihoodEighthDominantPairCore A) <
      thetaCuspLikelihoodEighthDominantSingleCore A := by
    calc
      (59 / 20 : ℝ) *
          (Real.exp (-(3 * A)) * thetaCuspLikelihoodEighthDominantPairCore A) =
          Real.exp (-(3 * A)) *
            ((59 / 20 : ℝ) * thetaCuspLikelihoodEighthDominantPairCore A) := by ring
      _ < Real.exp (-(3 * A)) *
          (thetaCuspLikelihoodEighthDominantTaylorTwenty A *
            thetaCuspLikelihoodEighthDominantSingleCore A) :=
        mul_lt_mul_of_pos_left hcore (Real.exp_pos _)
      _ = (Real.exp (-(3 * A)) *
          thetaCuspLikelihoodEighthDominantTaylorTwenty A) *
          thetaCuspLikelihoodEighthDominantSingleCore A := by ring
      _ ≤ 1 * thetaCuspLikelihoodEighthDominantSingleCore A := by gcongr
      _ = thetaCuspLikelihoodEighthDominantSingleCore A := one_mul _
  have hscale := mul_lt_mul_of_pos_left habsorb (Real.exp_pos (-(3 * A)))
  unfold thetaCuspLikelihoodEighthDominantPairMass
    thetaCuspLikelihoodEighthDominantSingleMass
  calc
    (59 / 20 : ℝ) *
        (Real.exp (-(6 * A)) * thetaCuspLikelihoodEighthDominantPairCore A) =
        Real.exp (-(3 * A)) * ((59 / 20 : ℝ) *
          (Real.exp (-(3 * A)) * thetaCuspLikelihoodEighthDominantPairCore A)) := by
      rw [show Real.exp (-(6 * A)) =
        Real.exp (-(3 * A)) * Real.exp (-(3 * A)) by
          rw [← Real.exp_add]
          congr 1
          ring]
      ring
    _ < Real.exp (-(3 * A)) * thetaCuspLikelihoodEighthDominantSingleCore A := hscale

/-- Scale-local Fock reserve retains `6368` dominant exponential units. -/
theorem sixThousandThreeHundredSixtyEight_mul_pow_eight_exp_lt_thetaCuspLikelihoodEighthFockOddWeight_of_18Over5_le
    {x : ℝ} (hx : 0 ≤ x)
    (hA : (18 / 5 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    6368 * thetaCuspSingleAtomReflectionScale 1 x ^ (8 : ℕ) *
        Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) <
      thetaCuspLikelihoodEighthFockOddWeight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hApi : Real.pi ≤ A :=
    (Real.pi_lt_d4.trans (by norm_num : (3.1416 : ℝ) < 18 / 5)).le.trans hA
  have hAseam : (157 / 50 : ℝ) ≤ A := by nlinarith [Real.pi_gt_d2]
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hdominant :=
    fiftyNineTwentieths_mul_thetaCuspLikelihoodEighthDominantPairMass_lt_singleMass_of_18Over5_le
      (A := A) (by simpa only [A] using hA)
  have htwo := thetaCuspLikelihoodAtomPairEighthScoreMass_two_two_eq hAseam hBA
  have hnondom := thetaCuspLikelihoodNonDominantPairEighthTail_le_sharp hApi hBA
  have hhigher := thetaCuspLikelihoodEighthHigherEvenFockLoss_le hx
  have hsingle :=
    tenThousandFiveHundredSeventyFive_mul_pow_eight_exp_lt_thetaCuspLikelihoodEighthDominantSingleMass_of_18Over5_le
      (by simpa only [A] using hA)
  have hscale : 0 < A ^ (8 : ℕ) * Real.exp (-(3 * A)) := by positivity
  have hhigher' : thetaCuspLikelihoodEighthHigherEvenFockLoss x ≤
      (1300 / 3 : ℝ) * A ^ (8 : ℕ) * Real.exp (-(3 * A)) := by
    simpa only [A] using hhigher
  unfold thetaCuspLikelihoodEighthFockOddWeight
  dsimp only [A, B]
  unfold thetaCuspLikelihoodEighthPairSectorMass
  rw [htwo]
  nlinarith [show
    (6368 : ℝ) + 376399 / 1999 + 1300 / 3 <
      (39 / 59 : ℝ) * 10575 by norm_num]

/-- Local normalization converts the Fock reserve into the literal eighth logarithmic floor. -/
theorem oneMillionSixHundredTwentyNineThousandOneHundredSixtyTwo_mul_pow_eight_exp_lt_thetaCuspLikelihoodSourceLogPartitionJetEight_of_18Over5_le
    {x : ℝ} (hx : 0 ≤ x)
    (hA : (18 / 5 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    1629162 * thetaCuspSingleAtomReflectionScale 1 x ^ (8 : ℕ) *
        Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) <
      thetaCuspLikelihoodSourceLogPartitionJetEight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let S := A ^ (8 : ℕ) * Real.exp (-(3 * A))
  let p := thetaCuspLikelihoodTailProbability B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hpSmall : 1560 * p < 1 := by
    simpa only [B, p] using
      oneThousandFiveHundredSixty_mul_thetaCuspLikelihoodTailProbability_lt_one_of_18Over5_le
        hx hA
  have hpEq : p = 1 - 1 / P := by
    have hPartEq := thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB
    have hden : 1 + thetaCuspHigherLikelihoodSpectralMoment B 0 ≠ 0 := by
      rw [← hPartEq]
      exact (by simpa only [P] using hP.ne')
    dsimp only [p, P, thetaCuspLikelihoodTailProbability,
      thetaCuspLikelihoodNormalizedMoment]
    rw [hPartEq]
    field_simp [hden]
    ring
  have hPinv : (1559 / 1560 : ℝ) < 1 / P := by
    rw [hpEq] at hpSmall
    linarith
  have hS : 0 < S := by
    dsimp only [S, A, thetaCuspSingleAtomReflectionScale]
    positivity
  have hweight :=
    sixThousandThreeHundredSixtyEight_mul_pow_eight_exp_lt_thetaCuspLikelihoodEighthFockOddWeight_of_18Over5_le
      hx hA
  have hlanding := scaled_thetaCuspLikelihoodEighthFockOddWeight_le_sourceLogPartitionJetEight hx
  have hfactor : 256 * (1559 / 1560 : ℝ) < 256 / P := by
    calc
      256 * (1559 / 1560 : ℝ) < 256 * (1 / P) :=
        mul_lt_mul_of_pos_left hPinv (by norm_num)
      _ = 256 / P := by ring
  have hleft : 1629162 * S <
      (256 * (1559 / 1560 : ℝ)) * (6368 * S) := by
    nlinarith
  have hfactorScaled :
      (256 * (1559 / 1560 : ℝ)) * (6368 * S) < (256 / P) * (6368 * S) :=
    mul_lt_mul_of_pos_right hfactor (by positivity)
  have hweightScaled : (256 / P) * (6368 * S) <
      (256 / P) * thetaCuspLikelihoodEighthFockOddWeight x := by
    apply mul_lt_mul_of_pos_left
    · simpa only [A, S, mul_assoc] using hweight
    · positivity
  calc
    1629162 * thetaCuspSingleAtomReflectionScale 1 x ^ (8 : ℕ) *
          Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) =
        1629162 * S := by dsimp only [A, S]; ring
    _ < (256 / P) * thetaCuspLikelihoodEighthFockOddWeight x :=
      hleft.trans (hfactorScaled.trans hweightScaled)
    _ ≤ thetaCuspLikelihoodSourceLogPartitionJetEight x := by
      simpa only [B, P] using hlanding

end

end RHTower
