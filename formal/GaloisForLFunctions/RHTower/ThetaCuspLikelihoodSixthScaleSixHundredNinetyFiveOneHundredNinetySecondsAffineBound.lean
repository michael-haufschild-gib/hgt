import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthStableTowerScaleSixHundredNinetyFiveOneHundredNinetySecondsBound
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodScaleLocalBellCoolingSixHundredNinetyFiveOneHundredNinetySeconds
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthScaleOneThousandThreeHundredNinetyOneThreeHundredEightyFourthsAffineBound

/-!
# Scale-695/192 affine upper bound for the sixth theta likelihood jet

The exact dominant atom-ray mass obeys `5693/20 - 480d`; the stable tower contributes less than
one quarter. Thus complete sixth mass is below `2849/10 - 480d`, and
`J₆ < (8016/125)(2849/10 - 480d)` on `695/192 ≤ A ≤ 1391/384`.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Exact rational score factor after extracting `exp(-3A)` at scale `695/192`. -/
def thetaCuspLikelihoodSixthScale695Over192DominantPolynomial (d : ℝ) : ℝ :=
  16 * thetaLikelihoodSixthScoreShift (119 / 64 + 3 * d) +
    18 * (1 / (407 / 192 + d)) *
      thetaLikelihoodSixthScoreRayTransformPolynomial
        ((695 / 192 + d) / (407 / 192 + d)) (119 / 64 + 3 * d)

/-- Cleared degree-fifteen certificate for the dominant affine budget. -/
theorem thetaCuspLikelihoodSixthScale695Over192DominantPolynomial_lt
    {d : ℝ} (hd : 0 ≤ d) (hdhi : d ≤ 1 / 384) :
    (1 / 51990 : ℝ) * (1 - 3 * d + (3 * d) ^ 2 / 2) *
        thetaCuspLikelihoodSixthScale695Over192DominantPolynomial d <
      5693 / 20 - 480 * d := by
  have hB : 0 < 407 / 192 + d := by linarith
  have hmul : (407 / 192 + d) ^ 7 *
      ((1 / 51990 : ℝ) * (1 - 3 * d + (3 * d) ^ 2 / 2) *
        thetaCuspLikelihoodSixthScale695Over192DominantPolynomial d) <
      (407 / 192 + d) ^ 7 * (5693 / 20 - 480 * d) := by
    dsimp [thetaCuspLikelihoodSixthScale695Over192DominantPolynomial,
      thetaLikelihoodSixthScoreRayTransformPolynomial,
      thetaLikelihoodSixthScoreShift, thetaLikelihoodSixthScoreShiftDerivOne,
      thetaLikelihoodSixthScoreShiftDerivTwo,
      thetaLikelihoodSixthScoreShiftDerivThree,
      thetaLikelihoodSixthScoreShiftDerivFour,
      thetaLikelihoodSixthScoreShiftDerivFive,
      thetaLikelihoodSixthScoreShiftDerivSix]
    field_simp [hB.ne']
    ring_nf
    rw [← sub_pos]
    ring_nf
    have hd2 : d ^ 2 ≤ (1 / 384 : ℝ) ^ 2 := pow_le_pow_left₀ hd hdhi 2
    have hd3 : d ^ 3 ≤ (1 / 384 : ℝ) ^ 3 := pow_le_pow_left₀ hd hdhi 3
    have hd4 : d ^ 4 ≤ (1 / 384 : ℝ) ^ 4 := pow_le_pow_left₀ hd hdhi 4
    have hd5 : d ^ 5 ≤ (1 / 384 : ℝ) ^ 5 := pow_le_pow_left₀ hd hdhi 5
    have hd6 : d ^ 6 ≤ (1 / 384 : ℝ) ^ 6 := pow_le_pow_left₀ hd hdhi 6
    have hd7 : d ^ 7 ≤ (1 / 384 : ℝ) ^ 7 := pow_le_pow_left₀ hd hdhi 7
    have hd8 : d ^ 8 ≤ (1 / 384 : ℝ) ^ 8 := pow_le_pow_left₀ hd hdhi 8
    have hd9 : d ^ 9 ≤ (1 / 384 : ℝ) ^ 9 := pow_le_pow_left₀ hd hdhi 9
    have hd10 : d ^ 10 ≤ (1 / 384 : ℝ) ^ 10 := pow_le_pow_left₀ hd hdhi 10
    have hd11 : d ^ 11 ≤ (1 / 384 : ℝ) ^ 11 := pow_le_pow_left₀ hd hdhi 11
    have hd12 : d ^ 12 ≤ (1 / 384 : ℝ) ^ 12 := pow_le_pow_left₀ hd hdhi 12
    have hd13 : d ^ 13 ≤ (1 / 384 : ℝ) ^ 13 := pow_le_pow_left₀ hd hdhi 13
    have hd14 : d ^ 14 ≤ (1 / 384 : ℝ) ^ 14 := pow_le_pow_left₀ hd hdhi 14
    have hd15 : d ^ 15 ≤ (1 / 384 : ℝ) ^ 15 := pow_le_pow_left₀ hd hdhi 15
    norm_num at hd2 hd3 hd4 hd5 hd6 hd7 hd8 hd9 hd10 hd11 hd12 hd13 hd14 hd15 ⊢
    nlinarith
  nlinarith [pow_pos hB 7]

/-- Sharp rational upper enclosure for `exp (-695/64)`. -/
theorem exp_neg_sixHundredNinetyFiveSixtyFourths_lt_oneOverFiftyOneThousandNineHundredNinety :
    Real.exp (-(695 / 64 : ℝ)) < (1 / 51990 : ℝ) := by
  have hbase := exp_neg_oneThousandThreeHundredNinetyOneOneHundredTwentyEighths_lt_oneOverFiftyTwoThousandFourHundred
  have hsmall : Real.exp (1 / 128 : ℝ) ≤ (128 / 127 : ℝ) := by
    convert Real.exp_bound_div_one_sub_of_interval
      (show (0 : ℝ) ≤ 1 / 128 by norm_num)
      (show (1 / 128 : ℝ) < 1 by norm_num) using 1 <;> norm_num
  have hprod : Real.exp (-(695 / 64 : ℝ)) =
      Real.exp (-(1391 / 128 : ℝ)) * Real.exp (1 / 128 : ℝ) := by
    rw [← Real.exp_add]
    congr 1
    norm_num
  rw [hprod]
  calc
    Real.exp (-(1391 / 128 : ℝ)) * Real.exp (1 / 128 : ℝ) <
        (1 / 52400 : ℝ) * Real.exp (1 / 128 : ℝ) := by gcongr
    _ ≤ (1 / 52400 : ℝ) * (128 / 127 : ℝ) := by gcongr
    _ < (1 / 51990 : ℝ) := by norm_num

/-- Dominant first atom-ray sixth mass obeys `5693/20 - 480d`. -/
theorem thetaCuspLikelihoodDominantAtomSixthScoreMass_lt_scale695Over192_affine
    (A : ℝ) {B : ℝ} (hAlo : (695 / 192 : ℝ) ≤ A) (hAhi : A ≤ 1391 / 384)
    (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodDominantAtomSixthScoreMass A B <
      5693 / 20 - 480 * (A - 695 / 192) := by
  have hB : 0 < B := by rw [hBA]; linarith
  let d := A - 695 / 192
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hdhi : d ≤ 1 / 384 := by dsimp only [d]; linarith
  have hAeq : A = 695 / 192 + d := by dsimp only [d]; ring
  have hBeq : B = 407 / 192 + d := by rw [hBA, hAeq]; ring
  have hy : 3 * A - 9 = 119 / 64 + 3 * d := by rw [hAeq]; ring
  have hextract :
      Real.exp (-(9 / 2 : ℝ)) * Real.exp (-(3 * B)) = Real.exp (-3 * A) := by
    rw [← Real.exp_add]
    congr 1
    rw [hBA]
    ring
  have hmassEq : thetaCuspLikelihoodDominantAtomSixthScoreMass A B =
      Real.exp (-3 * A) * thetaCuspLikelihoodSixthScale695Over192DominantPolynomial d := by
    rw [thetaCuspLikelihoodDominantAtomSixthScoreMass_eq A hB,
      thetaLikelihoodSixthScore_eq_shiftNine, hy]
    rw [show Real.exp (-(3 * B)) / B = Real.exp (-(3 * B)) * (1 / B) by ring]
    rw [show 16 * Real.exp (-(9 / 2 : ℝ)) *
          (thetaLikelihoodSixthScoreShift (119 / 64 + 3 * d) * Real.exp (-(3 * B))) +
        18 * Real.exp (-(9 / 2 : ℝ)) *
          (Real.exp (-(3 * B)) * (1 / B) *
            thetaLikelihoodSixthScoreRayTransformPolynomial (A / B) (119 / 64 + 3 * d)) =
        (Real.exp (-(9 / 2 : ℝ)) * Real.exp (-(3 * B))) *
          (16 * thetaLikelihoodSixthScoreShift (119 / 64 + 3 * d) +
            18 * (1 / B) *
              thetaLikelihoodSixthScoreRayTransformPolynomial
                (A / B) (119 / 64 + 3 * d)) by ring]
    rw [hextract, hAeq, hBeq]
    rfl
  have hexpd : Real.exp (-(3 * d)) ≤ 1 - 3 * d + (3 * d) ^ 2 / 2 :=
    exp_neg_le_quadratic (by positivity)
  have hExp : Real.exp (-3 * A) <
      (1 / 51990 : ℝ) * (1 - 3 * d + (3 * d) ^ 2 / 2) := by
    calc
      Real.exp (-3 * A) = Real.exp (-(695 / 64 : ℝ)) * Real.exp (-(3 * d)) := by
        rw [← Real.exp_add, hAeq]
        congr 1
        ring
      _ < (1 / 51990 : ℝ) * Real.exp (-(3 * d)) := by
        gcongr
        exact exp_neg_sixHundredNinetyFiveSixtyFourths_lt_oneOverFiftyOneThousandNineHundredNinety
      _ ≤ (1 / 51990 : ℝ) * (1 - 3 * d + (3 * d) ^ 2 / 2) := by gcongr
  have hpolypos : 0 < thetaCuspLikelihoodSixthScale695Over192DominantPolynomial d := by
    have hBd : 0 < 407 / 192 + d := by linarith
    dsimp [thetaCuspLikelihoodSixthScale695Over192DominantPolynomial,
      thetaLikelihoodSixthScoreRayTransformPolynomial,
      thetaLikelihoodSixthScoreShift, thetaLikelihoodSixthScoreShiftDerivOne,
      thetaLikelihoodSixthScoreShiftDerivTwo,
      thetaLikelihoodSixthScoreShiftDerivThree,
      thetaLikelihoodSixthScoreShiftDerivFour,
      thetaLikelihoodSixthScoreShiftDerivFive,
      thetaLikelihoodSixthScoreShiftDerivSix]
    field_simp [hBd.ne']
    ring_nf
    positivity
  rw [hmassEq]
  calc
    _ < ((1 / 51990 : ℝ) * (1 - 3 * d + (3 * d) ^ 2 / 2)) *
        thetaCuspLikelihoodSixthScale695Over192DominantPolynomial d := by gcongr
    _ < 5693 / 20 - 480 * d := by
      simpa only [mul_assoc] using
        thetaCuspLikelihoodSixthScale695Over192DominantPolynomial_lt hd hdhi
    _ = 5693 / 20 - 480 * (A - 695 / 192) := by rfl

/-- Dominant plus stable sixth-score mass is below `2849/10 - 480d`. -/
theorem integral_thetaLikelihoodSixthScore_lt_scale695Over192_affine
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (695 / 192 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 1391 / 384) :
    (∫ t : ℝ,
        thetaLikelihoodSixthScore (thetaCuspSingleAtomReflectionScale 1 x * t) *
          Real.exp (-(thetaCuspLikelihoodCoordinate x * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure) <
      2849 / 10 - 480 * (thetaCuspSingleAtomReflectionScale 1 x - 695 / 192) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hd := thetaCuspLikelihoodDominantAtomSixthScoreMass_lt_scale695Over192_affine
    A (by simpa only [A] using hAlo) (by simpa only [A] using hAhi) hBA
  have hs := tsum_thetaCuspLikelihoodStableAtomSixthScoreMass_lt_oneQuarter_of_695Over192_le
    (by simpa only [A] using hAlo) hBA
  rw [thetaCuspLikelihoodSixthScoreIntegral_eq_dominant_add_stable hx]
  dsimp only [A, B] at hd hs ⊢
  nlinarith

/-- Affine logarithmic sixth-jet ceiling on the scale-`695/192` chamber. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetSix_lt_scale695Over192_affine
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (695 / 192 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 1391 / 384) :
    thetaCuspLikelihoodSourceLogPartitionJetSix x <
      (8016 / 125 : ℝ) *
        (2849 / 10 - 480 * (thetaCuspSingleAtomReflectionScale 1 x - 695 / 192)) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let massBudget := 2849 / 10 - 480 * (A - 695 / 192)
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hPone : 1 ≤ P := by
    have hzero := thetaCuspHigherLikelihoodSpectralMoment_nonneg (B := B) 0
    change 1 ≤ thetaCuspLikelihoodPartition B
    rw [thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB]
    linarith
  have hbudget : 0 < massBudget := by dsimp only [massBudget, A]; linarith
  have hscore :
      (∫ t : ℝ, thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t))
          ∂thetaCuspHigherLikelihoodSpectralMeasure) < massBudget := by
    simpa only [A, B, massBudget] using
      integral_thetaLikelihoodSixthScore_lt_scale695Over192_affine hx hAlo hAhi
  have hordinary : thetaCuspLikelihoodSourceOrdinaryJetSix x < 64 * massBudget := by
    have hordinaryPos := thetaCuspLikelihoodSourceOrdinaryJetSix_pos hx
    rw [thetaCuspLikelihoodSourceOrdinaryJetSix_eq_spectralIntegral hx]
    rw [thetaCuspLikelihoodSourceOrdinaryJetSix_eq_spectralIntegral hx] at hordinaryPos
    have hcoeff : 0 < 64 / P := div_pos (by norm_num) hP
    have hcoeffUpper : 64 / P ≤ 64 := by
      apply (div_le_iff₀ hP).2
      nlinarith
    have hmass0 : 0 < (∫ t : ℝ,
        thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure) := by
      dsimp only [A, B] at hordinaryPos ⊢
      nlinarith
    dsimp only [A, B] at hscore ⊢
    nlinarith [mul_lt_mul_of_pos_left hscore hcoeff,
      mul_le_mul_of_nonneg_right hcoeffUpper hmass0.le]
  have hlog :=
    thetaCuspLikelihoodSourceLogPartitionJetSix_lt_fiveHundredOneFiveHundredths_ordinary_of_695Over192_le
      hx hAlo
  dsimp only [massBudget, A] at hordinary ⊢
  nlinarith

/-- Weight-coordinate form of the scale-`695/192` sixth ceiling. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetSix_lt_scale695Over192_affine_weight
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (695 / 192 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 1391 / 384) :
    thetaCuspLikelihoodSourceLogPartitionJetSix x <
      (8016 / 125 : ℝ) *
        (6512 / 5 - 480 * thetaCuspBornWittenWeight 1 x) := by
  have hscale : thetaCuspSingleAtomReflectionScale 1 x =
      thetaCuspBornWittenWeight 1 x + 3 / 2 := by
    dsimp only [thetaCuspSingleAtomReflectionScale]
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ 2 = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have h := thetaCuspLikelihoodSourceLogPartitionJetSix_lt_scale695Over192_affine
    hx hAlo hAhi
  rw [hscale] at h
  convert h using 1
  all_goals ring

end
end RHTower
