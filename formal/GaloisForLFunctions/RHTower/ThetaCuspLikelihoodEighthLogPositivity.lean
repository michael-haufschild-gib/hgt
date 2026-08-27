import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodEighthPairSectorTrace

/-!
# Positive literal eighth logarithmic likelihood jet

Exact pair-sector and higher-even Bell losses fit beneath one normalized Fock
scale.  The positive residual therefore survives in the literal eighth jet of
the logarithmic likelihood partition on the full physical source half-line.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

/-- The ordinary eighth source trace contains the dominant one-particle mass
with the exact Bell normalization. -/
theorem thetaCuspLikelihoodSourceOrdinaryJetEight_ge_scaledDominantSingleMass
    {x : ℝ} (hx : 0 ≤ x) :
    (256 / thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x)) *
        thetaCuspLikelihoodEighthDominantSingleMass
          (thetaCuspSingleAtomReflectionScale 1 x) ≤
      thetaCuspLikelihoodSourceOrdinaryJetEight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let total := ∑' k : ℕ, thetaCuspLikelihoodAtomEighthScoreMass (k + 2) A B
  have hA : Real.pi ≤ A := by
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    nlinarith [Real.pi_pos]
  have hApi : (157 / 50 : ℝ) ≤ A := by nlinarith [Real.pi_gt_d2]
  have hBA : B = A - 3 / 2 := by
    dsimp only [A, B]
    unfold thetaCuspLikelihoodCoordinate thetaCuspSingleAtomReflectionScale
    norm_num
    rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hs := summable_thetaCuspLikelihoodAtomEighthScoreMass A hB
  have hstable : 0 ≤
      ∑' k : ℕ, thetaCuspLikelihoodAtomEighthScoreMass (k + 3) A B := by
    exact tsum_nonneg fun k =>
      (thetaCuspLikelihoodStableAtomEighthScoreMass_pos
        (n := k + 3) (by omega) hA hBA).le
  have htotalSplit : total =
      thetaCuspLikelihoodAtomEighthScoreMass 2 A B +
        ∑' k : ℕ, thetaCuspLikelihoodAtomEighthScoreMass (k + 3) A B := by
    dsimp only [total]
    simpa only [Nat.add_assoc] using hs.tsum_eq_zero_add
  have hdominantEq :=
    thetaCuspLikelihoodEighthDominantSingleMass_eq_atomScoreMass hApi hBA
  have hdominantLe : thetaCuspLikelihoodEighthDominantSingleMass A ≤ total := by
    rw [htotalSplit, hdominantEq]
    linarith
  have hsource := thetaCuspLikelihoodSourceOrdinaryJetEight_eq_spectralIntegral hx
  have hintegral := integral_thetaCuspLikelihoodEighthSourceScore_eq_tsum_atom A hB
  have hsourceEq : thetaCuspLikelihoodSourceOrdinaryJetEight x = 256 / P * total := by
    rw [hsource, hintegral]
  rw [hsourceEq]
  exact mul_le_mul_of_nonneg_left hdominantLe (by positivity)

/-- All negative even Bell grades leave a strict part of the ordinary leading trace. -/
theorem thetaCuspLikelihoodEighthBellEvenLoss_lt_leading
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodEighthBellGradeTwo x +
          6 * thetaCuspLikelihoodEighthBellGradeFour x +
          120 * thetaCuspLikelihoodEighthBellGradeSix x +
          5040 * thetaCuspLikelihoodEighthBellGradeEight x <
      thetaCuspLikelihoodEighthBellJetEight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let pair := thetaCuspLikelihoodEighthPairSectorMass A B
  let higher := thetaCuspLikelihoodEighthHigherEvenFockLoss x
  let dominant := thetaCuspLikelihoodEighthDominantSingleMass A
  let weight := thetaCuspLikelihoodEighthFockOddWeight x
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hr : 0 ≤ thetaCuspHigherLikelihoodSpectralResponse B := by
    rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
    exact thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hPeq : P = 1 + thetaCuspHigherLikelihoodSpectralResponse B := by
    dsimp only [P]
    rw [thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB,
      thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
  have hPone : 1 ≤ P := by rw [hPeq]; linarith
  have hA : Real.pi ≤ A := by
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    nlinarith [Real.pi_pos]
  have hBA : B = A - 3 / 2 := by
    dsimp only [A, B]
    unfold thetaCuspLikelihoodCoordinate thetaCuspSingleAtomReflectionScale
    norm_num
    rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hpairPos : 0 < pair := by
    simpa only [pair] using thetaCuspLikelihoodEighthPairSectorMass_pos hA hBA
  have hfactorComp : 128 / P ^ 2 ≤ 256 / P := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hP) hP).2
    nlinarith [sq_nonneg P]
  have hgradeTwo := thetaCuspLikelihoodEighthBellGradeTwo_le_algebraicPairTrace hx
  rw [thetaCuspLikelihoodEighthAlgebraicPairTrace_eq_pairSectorMass hx] at hgradeTwo
  have hgradeTwoScaled :
      thetaCuspLikelihoodEighthBellGradeTwo x ≤ 256 / P * pair := by
    exact hgradeTwo.trans (mul_le_mul_of_nonneg_right hfactorComp hpairPos.le)
  have hhigher := thetaCuspLikelihoodEighthBellHigherEvenLoss_le_fock hx
  have hloss :
      thetaCuspLikelihoodEighthBellGradeTwo x +
            (6 * thetaCuspLikelihoodEighthBellGradeFour x +
              120 * thetaCuspLikelihoodEighthBellGradeSix x +
              5040 * thetaCuspLikelihoodEighthBellGradeEight x) ≤
        256 / P * (pair + higher) := by
    calc
      _ ≤ 256 / P * pair + 256 / P * higher := add_le_add hgradeTwoScaled hhigher
      _ = 256 / P * (pair + higher) := by ring
  have hsource :=
    thetaCuspLikelihoodSourceOrdinaryJetEight_ge_scaledDominantSingleMass hx
  have hleading : 256 / P * dominant ≤ thetaCuspLikelihoodEighthBellJetEight x := by
    simpa only [A, B, P, dominant, thetaCuspLikelihoodEighthBellJetEight] using hsource
  have hweight : 0 < weight := by
    simpa only [weight] using thetaCuspLikelihoodEighthFockOddWeight_pos hx
  have hfactor : 0 < 256 / P := div_pos (by norm_num) hP
  have hscaledWeight : 0 < 256 / P * weight := mul_pos hfactor hweight
  have hweightEq : weight = dominant - (pair + higher) := by
    rfl
  rw [hweightEq] at hscaledWeight
  nlinarith

/-- Literal eighth logarithmic likelihood jet is strictly positive on the physical seam. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetEight_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspLikelihoodSourceLogPartitionJetEight x := by
  have hlower := thetaCuspLikelihoodEighthBellEvenLoss_lower_le_sourceLogJet hx
  have hgap := thetaCuspLikelihoodEighthBellEvenLoss_lt_leading hx
  nlinarith


/-- The completed eighth Fock reserve retains five hundred dominant exponential units. -/
theorem fiveHundred_mul_pow_eight_exp_lt_thetaCuspLikelihoodEighthFockOddWeight
    {x : ℝ} (hx : 0 ≤ x) :
    500 * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) <
      thetaCuspLikelihoodEighthFockOddWeight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hA : Real.pi ≤ A := by
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    nlinarith [Real.pi_pos]
  have hApi : (157 / 50 : ℝ) ≤ A := by nlinarith [Real.pi_gt_d2]
  have hBA : B = A - 3 / 2 := by
    dsimp only [A, B]
    unfold thetaCuspLikelihoodCoordinate thetaCuspSingleAtomReflectionScale
    norm_num
    rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hdominant :=
    three_halves_mul_thetaCuspLikelihoodEighthDominantPairMass_lt_singleMass hApi
  have htwo := thetaCuspLikelihoodAtomPairEighthScoreMass_two_two_eq hApi hBA
  have hnondom := thetaCuspLikelihoodNonDominantPairEighthTail_le_sharp hA hBA
  have hhigher := thetaCuspLikelihoodEighthHigherEvenFockLoss_le hx
  have hsingle :=
    seventeenThousandFourHundredNinetySixFifths_mul_pow_eight_exp_lt_dominantSingleMass
      hA hBA
  have hscale : 0 < A ^ 8 * Real.exp (-(3 * A)) := by
    have hA0 : 0 < A := Real.pi_pos.trans_le hA
    positivity
  have hhigher' : thetaCuspLikelihoodEighthHigherEvenFockLoss x ≤
      (1300 / 3 : ℝ) * A ^ 8 * Real.exp (-(3 * A)) := by
    simpa only [A] using hhigher
  unfold thetaCuspLikelihoodEighthFockOddWeight
  dsimp only [A, B]
  unfold thetaCuspLikelihoodEighthPairSectorMass
  rw [htwo]
  nlinarith [show
    (500 : ℝ) + 376399 / 1999 + 1300 / 3 < 5832 / 5 by norm_num]

/-- Exact normalized Fock reserve lies below the literal logarithmic eighth jet. -/
theorem scaled_thetaCuspLikelihoodEighthFockOddWeight_le_sourceLogPartitionJetEight
    {x : ℝ} (hx : 0 ≤ x) :
    (256 / thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x)) *
        thetaCuspLikelihoodEighthFockOddWeight x ≤
      thetaCuspLikelihoodSourceLogPartitionJetEight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let pair := thetaCuspLikelihoodEighthPairSectorMass A B
  let higher := thetaCuspLikelihoodEighthHigherEvenFockLoss x
  let dominant := thetaCuspLikelihoodEighthDominantSingleMass A
  let weight := thetaCuspLikelihoodEighthFockOddWeight x
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hr : 0 ≤ thetaCuspHigherLikelihoodSpectralResponse B := by
    rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
    exact thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hPeq : P = 1 + thetaCuspHigherLikelihoodSpectralResponse B := by
    dsimp only [P]
    rw [thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB,
      thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
  have hPone : 1 ≤ P := by rw [hPeq]; linarith
  have hA : Real.pi ≤ A := by
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    nlinarith [Real.pi_pos]
  have hBA : B = A - 3 / 2 := by
    dsimp only [A, B]
    unfold thetaCuspLikelihoodCoordinate thetaCuspSingleAtomReflectionScale
    norm_num
    rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hpairPos : 0 < pair := by
    simpa only [pair] using thetaCuspLikelihoodEighthPairSectorMass_pos hA hBA
  have hfactorComp : 128 / P ^ 2 ≤ 256 / P := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hP) hP).2
    nlinarith [sq_nonneg P]
  have hgradeTwo := thetaCuspLikelihoodEighthBellGradeTwo_le_algebraicPairTrace hx
  rw [thetaCuspLikelihoodEighthAlgebraicPairTrace_eq_pairSectorMass hx] at hgradeTwo
  have hgradeTwoScaled :
      thetaCuspLikelihoodEighthBellGradeTwo x ≤ 256 / P * pair := by
    exact hgradeTwo.trans (mul_le_mul_of_nonneg_right hfactorComp hpairPos.le)
  have hhigher := thetaCuspLikelihoodEighthBellHigherEvenLoss_le_fock hx
  have hloss :
      thetaCuspLikelihoodEighthBellGradeTwo x +
            (6 * thetaCuspLikelihoodEighthBellGradeFour x +
              120 * thetaCuspLikelihoodEighthBellGradeSix x +
              5040 * thetaCuspLikelihoodEighthBellGradeEight x) ≤
        256 / P * (pair + higher) := by
    calc
      _ ≤ 256 / P * pair + 256 / P * higher := add_le_add hgradeTwoScaled hhigher
      _ = 256 / P * (pair + higher) := by ring
  have hsource :=
    thetaCuspLikelihoodSourceOrdinaryJetEight_ge_scaledDominantSingleMass hx
  have hleading : 256 / P * dominant ≤ thetaCuspLikelihoodEighthBellJetEight x := by
    simpa only [A, B, P, dominant, thetaCuspLikelihoodEighthBellJetEight] using hsource
  have hlower := thetaCuspLikelihoodEighthBellEvenLoss_lower_le_sourceLogJet hx
  have hweightEq : weight = dominant - (pair + higher) := by rfl
  change 256 / P * weight ≤ thetaCuspLikelihoodSourceLogPartitionJetEight x
  rw [hweightEq]
  nlinarith

/-- Quantitative literal logarithmic eighth-jet floor at the physical source scale. -/
theorem sixtyFourThousand_mul_pow_eight_exp_lt_thetaCuspLikelihoodSourceLogPartitionJetEight
    {x : ℝ} (hx : 0 ≤ x) :
    64000 * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) <
      thetaCuspLikelihoodSourceLogPartitionJetEight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let S := A ^ 8 * Real.exp (-(3 * A))
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hr : 0 ≤ thetaCuspHigherLikelihoodSpectralResponse B := by
    rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
    exact thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hrSmall : 399 * thetaCuspHigherLikelihoodSpectralResponse B < 1 := by
    simpa only [B] using
      three_hundred_ninety_nine_mul_thetaCuspHigherLikelihoodSpectralResponse_lt_one hx
  have hPeq : P = 1 + thetaCuspHigherLikelihoodSpectralResponse B := by
    dsimp only [P]
    rw [thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB,
      thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
  have hPtwo : P < 2 := by rw [hPeq]; nlinarith
  have hfactor : 128 < 256 / P := by
    apply (lt_div_iff₀ hP).2
    nlinarith
  have hS : 0 < S := by
    have hA : 0 < A := by
      exact Real.pi_pos.trans_le (by
        dsimp only [A, thetaCuspSingleAtomReflectionScale]
        norm_num
        have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
        nlinarith [Real.pi_pos])
    dsimp only [S]
    positivity
  have hmargin :=
    fiveHundred_mul_pow_eight_exp_lt_thetaCuspLikelihoodEighthFockOddWeight hx
  have hlanding :=
    scaled_thetaCuspLikelihoodEighthFockOddWeight_le_sourceLogPartitionJetEight hx
  have hleft : 64000 * S < (256 / P) * (500 * S) := by
    nlinarith [mul_pos (sub_pos.mpr hfactor) hS]
  have hmiddle : (256 / P) * (500 * S) <
      (256 / P) * thetaCuspLikelihoodEighthFockOddWeight x := by
    exact mul_lt_mul_of_pos_left (by simpa only [A, S, mul_assoc] using hmargin)
      (div_pos (by norm_num) hP)
  calc
    64000 * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
          Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) =
        64000 * S := by dsimp only [A, S]; ring
    _ < thetaCuspLikelihoodSourceLogPartitionJetEight x :=
      hleft.trans (hmiddle.trans_le (by simpa only [B, P] using hlanding))

end

end RHTower
