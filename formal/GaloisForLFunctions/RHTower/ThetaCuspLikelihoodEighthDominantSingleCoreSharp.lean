import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodEighthLogPositivity
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodHighCumulantCalibration

/-!
# Sharp dominant one-particle eighth core

The exact Dirac--ray one-particle core admits a uniform algebraic floor of `9549 A^8`
on the entire physical source chamber `A ≥ 157/50`.  This replaces the earlier indirect
floor `17496/5 A^8`, and leaves `2561` exponential units after complete pair and higher-even
Fock losses.  Global partition normalization then gives the literal logarithmic floor
`653976 A^8 exp(-3A) < J₈`.
-/

namespace RHTower

noncomputable section

set_option maxRecDepth 20000 in
/-- Exact algebraic floor for the dominant one-particle core on the physical chamber. -/
theorem nineThousandFiveHundredFortyNine_mul_pow_eight_lt_thetaCuspLikelihoodEighthDominantSingleCore
    {A : ℝ} (hA : (157 / 50 : ℝ) ≤ A) :
    9549 * A ^ 8 < thetaCuspLikelihoodEighthDominantSingleCore A := by
  let B := A - 3 / 2
  have hB : 0 < B := by
    dsimp only [B]
    linarith
  change 9549 * A ^ 8 <
    16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
      18 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (3 * A)
  let s := A - 157 / 50
  have hs : 0 ≤ s := by
    dsimp only [s]
    linarith
  have hmul : 0 < B ^ 9 *
      (16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
        18 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (3 * A) -
        9549 * A ^ 8) := by
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
    rw [show A = 157 / 50 + s by dsimp only [s]; ring]
    ring_nf
    positivity
  have hdiff : 0 <
      16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
        18 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (3 * A) -
        9549 * A ^ 8 :=
    pos_of_mul_pos_right hmul (pow_nonneg hB.le 9)
  linarith

/-- Restoring the exact dominant exponential preserves the sharp core floor. -/
theorem nineThousandFiveHundredFortyNine_mul_pow_eight_exp_lt_thetaCuspLikelihoodEighthDominantSingleMass
    {A : ℝ} (hA : (157 / 50 : ℝ) ≤ A) :
    9549 * A ^ 8 * Real.exp (-(3 * A)) <
      thetaCuspLikelihoodEighthDominantSingleMass A := by
  have hcore :=
    nineThousandFiveHundredFortyNine_mul_pow_eight_lt_thetaCuspLikelihoodEighthDominantSingleCore hA
  have hscaled := mul_lt_mul_of_pos_left hcore (Real.exp_pos (-(3 * A)))
  unfold thetaCuspLikelihoodEighthDominantSingleMass
  nlinarith

/-- Complete global Fock reserve after dominant-pair, non-dominant-pair, and higher-even loss. -/
theorem twoThousandFiveHundredSixtyOne_mul_pow_eight_exp_lt_thetaCuspLikelihoodEighthFockOddWeight
    {x : ℝ} (hx : 0 ≤ x) :
    2561 * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) <
      thetaCuspLikelihoodEighthFockOddWeight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hApi : Real.pi ≤ A := by
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    nlinarith [Real.pi_pos]
  have hAseam : (157 / 50 : ℝ) ≤ A := by nlinarith [Real.pi_gt_d2]
  have hBA : B = A - 3 / 2 := by
    dsimp only [A, B, thetaCuspSingleAtomReflectionScale, thetaCuspLikelihoodCoordinate]
    norm_num
    rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hdominant :=
    three_halves_mul_thetaCuspLikelihoodEighthDominantPairMass_lt_singleMass hAseam
  have htwo := thetaCuspLikelihoodAtomPairEighthScoreMass_two_two_eq hAseam hBA
  have hnondom := thetaCuspLikelihoodNonDominantPairEighthTail_le_sharp hApi hBA
  have hhigher := thetaCuspLikelihoodEighthHigherEvenFockLoss_le hx
  have hsingle :=
    nineThousandFiveHundredFortyNine_mul_pow_eight_exp_lt_thetaCuspLikelihoodEighthDominantSingleMass
      hAseam
  have hscale : 0 < A ^ 8 * Real.exp (-(3 * A)) := by positivity
  have hhigher' : thetaCuspLikelihoodEighthHigherEvenFockLoss x ≤
      (1300 / 3 : ℝ) * A ^ 8 * Real.exp (-(3 * A)) := by
    simpa only [A] using hhigher
  unfold thetaCuspLikelihoodEighthFockOddWeight
  dsimp only [A, B]
  unfold thetaCuspLikelihoodEighthPairSectorMass
  rw [htwo]
  nlinarith [show
    (2561 : ℝ) + 376399 / 1999 + 1300 / 3 < (1 / 3 : ℝ) * 9549 by norm_num]

/-- Global partition normalization converts the sharp Fock reserve into a literal log floor. -/
theorem sixHundredFiftyThreeThousandNineHundredSeventySix_mul_pow_eight_exp_lt_thetaCuspLikelihoodSourceLogPartitionJetEight
    {x : ℝ} (hx : 0 ≤ x) :
    653976 * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) <
      thetaCuspLikelihoodSourceLogPartitionJetEight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let S := A ^ 8 * Real.exp (-(3 * A))
  let p := thetaCuspLikelihoodTailProbability B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hApos : 0 < A := by
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    positivity
  have hpSmall : 400 * p < 1 := by
    simpa only [B, p] using
      four_hundred_mul_thetaCuspLikelihoodTailProbability_coordinate_lt_one hx
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
  have hPinv : (399 / 400 : ℝ) < 1 / P := by
    rw [hpEq] at hpSmall
    linarith
  have hS : 0 < S := by
    dsimp only [S]
    positivity
  have hweight :=
    twoThousandFiveHundredSixtyOne_mul_pow_eight_exp_lt_thetaCuspLikelihoodEighthFockOddWeight
      hx
  have hlanding := scaled_thetaCuspLikelihoodEighthFockOddWeight_le_sourceLogPartitionJetEight hx
  have hfactor : 256 * (399 / 400 : ℝ) < 256 / P := by
    calc
      256 * (399 / 400 : ℝ) < 256 * (1 / P) :=
        mul_lt_mul_of_pos_left hPinv (by norm_num)
      _ = 256 / P := by ring
  have hleft : 653976 * S <
      (256 * (399 / 400 : ℝ)) * (2561 * S) := by
    nlinarith
  have hfactorScaled :
      (256 * (399 / 400 : ℝ)) * (2561 * S) < (256 / P) * (2561 * S) :=
    mul_lt_mul_of_pos_right hfactor (by positivity)
  have hweightScaled : (256 / P) * (2561 * S) <
      (256 / P) * thetaCuspLikelihoodEighthFockOddWeight x := by
    apply mul_lt_mul_of_pos_left
    · simpa only [A, S, mul_assoc] using hweight
    · positivity
  calc
    653976 * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
          Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) =
        653976 * S := by dsimp only [A, S]; ring
    _ < (256 / P) * thetaCuspLikelihoodEighthFockOddWeight x :=
      hleft.trans (hfactorScaled.trans hweightScaled)
    _ ≤ thetaCuspLikelihoodSourceLogPartitionJetEight x := by
      simpa only [B, P] using hlanding

end

end RHTower
