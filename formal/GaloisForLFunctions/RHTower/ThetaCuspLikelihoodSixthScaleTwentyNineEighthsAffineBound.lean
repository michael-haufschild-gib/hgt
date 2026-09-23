import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthStableTowerScaleTwentyNineEighthsBound
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodScaleLocalBellCoolingTwentyNineEighths
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthScaleElevenThirdsAffineBound
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomHighOrderQuadrature

/-!
# Scale-29/8 affine upper bound for the sixth theta likelihood jet

The exact dominant atom-ray mass obeys `282 - 480d`; the stable tower contributes less than
one half.  The sharper local Bell factor then gives
`J₆ < (40076/625)(565/2 - 480d)` on `29/8 ≤ A ≤ 175/48`.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Exact rational score factor after extracting `exp(-3A)` at scale `29/8`. -/
def thetaCuspLikelihoodSixthScale29Over8DominantPolynomial (d : ℝ) : ℝ :=
  16 * thetaLikelihoodSixthScoreShift (15 / 8 + 3 * d) +
    18 * (1 / (17 / 8 + d)) *
      thetaLikelihoodSixthScoreRayTransformPolynomial
        ((29 / 8 + d) / (17 / 8 + d)) (15 / 8 + 3 * d)

/-- Cleared degree-fifteen certificate for the dominant affine budget. -/
theorem thetaCuspLikelihoodSixthScale29Over8DominantPolynomial_lt
    {d : ℝ} (hd : 0 ≤ d) (hdhi : d ≤ 1 / 48) :
    (1 / 52800 : ℝ) * (1 - 3 * d + (3 * d) ^ (2 : ℕ) / 2) *
        thetaCuspLikelihoodSixthScale29Over8DominantPolynomial d <
      282 - 480 * d := by
  have hB : 0 < 17 / 8 + d := by linarith
  have hmul : (17 / 8 + d) ^ (7 : ℕ) *
      ((1 / 52800 : ℝ) * (1 - 3 * d + (3 * d) ^ (2 : ℕ) / 2) *
        thetaCuspLikelihoodSixthScale29Over8DominantPolynomial d) <
      (17 / 8 + d) ^ (7 : ℕ) * (282 - 480 * d) := by
    dsimp [thetaCuspLikelihoodSixthScale29Over8DominantPolynomial,
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
    have hd2 : d ^ (2 : ℕ) ≤ (1 / 48 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ hd hdhi 2
    have hd3 : d ^ (3 : ℕ) ≤ (1 / 48 : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ hd hdhi 3
    have hd4 : d ^ (4 : ℕ) ≤ (1 / 48 : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ hd hdhi 4
    have hd5 : d ^ (5 : ℕ) ≤ (1 / 48 : ℝ) ^ (5 : ℕ) := pow_le_pow_left₀ hd hdhi 5
    have hd6 : d ^ (6 : ℕ) ≤ (1 / 48 : ℝ) ^ (6 : ℕ) := pow_le_pow_left₀ hd hdhi 6
    have hd7 : d ^ (7 : ℕ) ≤ (1 / 48 : ℝ) ^ (7 : ℕ) := pow_le_pow_left₀ hd hdhi 7
    have hd8 : d ^ (8 : ℕ) ≤ (1 / 48 : ℝ) ^ (8 : ℕ) := pow_le_pow_left₀ hd hdhi 8
    have hd9 : d ^ (9 : ℕ) ≤ (1 / 48 : ℝ) ^ (9 : ℕ) := pow_le_pow_left₀ hd hdhi 9
    have hd10 : d ^ (10 : ℕ) ≤ (1 / 48 : ℝ) ^ (10 : ℕ) := pow_le_pow_left₀ hd hdhi 10
    have hd11 : d ^ (11 : ℕ) ≤ (1 / 48 : ℝ) ^ (11 : ℕ) := pow_le_pow_left₀ hd hdhi 11
    have hd12 : d ^ (12 : ℕ) ≤ (1 / 48 : ℝ) ^ (12 : ℕ) := pow_le_pow_left₀ hd hdhi 12
    have hd13 : d ^ (13 : ℕ) ≤ (1 / 48 : ℝ) ^ (13 : ℕ) := pow_le_pow_left₀ hd hdhi 13
    have hd14 : d ^ (14 : ℕ) ≤ (1 / 48 : ℝ) ^ (14 : ℕ) := pow_le_pow_left₀ hd hdhi 14
    have hd15 : d ^ (15 : ℕ) ≤ (1 / 48 : ℝ) ^ (15 : ℕ) := pow_le_pow_left₀ hd hdhi 15
    norm_num at hd2 hd3 hd4 hd5 hd6 hd7 hd8 hd9 hd10 hd11 hd12 hd13 hd14 hd15 ⊢
    nlinarith
  nlinarith [pow_pos hB 7]

/-- Rational upper enclosure for `exp (-87/8)`. -/
theorem exp_neg_eightySevenEighths_lt_oneOverFiftyTwoThousandEightHundred :
    Real.exp (-(87 / 8 : ℝ)) < (1 / 52800 : ℝ) := by
  have hneg11 : Real.exp (-11) < (10 / 598741 : ℝ) :=
    exp_neg_eleven_lt_tenOverFiveHundredNinetyEightThousandSevenHundredFortyOne
  have hsmall := exp_le_thetaCuspThirtySecondExpTaylorUpper_pow 4
  have hfactor : Real.exp (1 / 8 : ℝ) ≤
      thetaCuspThirtySecondExpTaylorUpper ^ (4 : ℕ) := by
    convert hsmall using 1 <;> norm_num
  have hproduct : Real.exp (-(87 / 8 : ℝ)) =
      Real.exp (-11) * Real.exp (1 / 8) := by
    rw [← Real.exp_add]
    congr 1
    norm_num
  rw [hproduct]
  have hpowpos : 0 < thetaCuspThirtySecondExpTaylorUpper ^ (4 : ℕ) := by
    norm_num [thetaCuspThirtySecondExpTaylorUpper,
      thetaCuspExpTwoTaylorEightUpperPolynomial,
      thetaCuspExpTwoTaylorEightPolynomial]
  have hupper : Real.exp (-11) * Real.exp (1 / 8) <
      (10 / 598741 : ℝ) * thetaCuspThirtySecondExpTaylorUpper ^ (4 : ℕ) :=
    (mul_le_mul_of_nonneg_left hfactor (Real.exp_pos _).le).trans_lt
      (mul_lt_mul_of_pos_right hneg11 hpowpos)
  exact hupper.trans (show
      (10 / 598741 : ℝ) * thetaCuspThirtySecondExpTaylorUpper ^ (4 : ℕ) <
        (1 / 52800 : ℝ) by
      norm_num [thetaCuspThirtySecondExpTaylorUpper,
        thetaCuspExpTwoTaylorEightUpperPolynomial,
        thetaCuspExpTwoTaylorEightPolynomial])

/-- Dominant first atom-ray sixth mass obeys `282 - 480d`. -/
theorem thetaCuspLikelihoodDominantAtomSixthScoreMass_lt_scale29Over8_affine
    (A : ℝ) {B : ℝ} (hAlo : (29 / 8 : ℝ) ≤ A) (hAhi : A ≤ 175 / 48)
    (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodDominantAtomSixthScoreMass A B <
      282 - 480 * (A - 29 / 8) := by
  have hB : 0 < B := by rw [hBA]; linarith
  let d := A - 29 / 8
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hdhi : d ≤ 1 / 48 := by dsimp only [d]; linarith
  have hAeq : A = 29 / 8 + d := by dsimp only [d]; ring
  have hBeq : B = 17 / 8 + d := by rw [hBA, hAeq]; ring
  have hy : 3 * A - 9 = 15 / 8 + 3 * d := by rw [hAeq]; ring
  have hextract :
      Real.exp (-(9 / 2 : ℝ)) * Real.exp (-(3 * B)) = Real.exp (-3 * A) := by
    rw [← Real.exp_add]
    congr 1
    rw [hBA]
    ring
  have hmassEq : thetaCuspLikelihoodDominantAtomSixthScoreMass A B =
      Real.exp (-3 * A) * thetaCuspLikelihoodSixthScale29Over8DominantPolynomial d := by
    rw [thetaCuspLikelihoodDominantAtomSixthScoreMass_eq A hB,
      thetaLikelihoodSixthScore_eq_shiftNine, hy]
    rw [show Real.exp (-(3 * B)) / B = Real.exp (-(3 * B)) * (1 / B) by ring]
    rw [show 16 * Real.exp (-(9 / 2 : ℝ)) *
          (thetaLikelihoodSixthScoreShift (15 / 8 + 3 * d) * Real.exp (-(3 * B))) +
        18 * Real.exp (-(9 / 2 : ℝ)) *
          (Real.exp (-(3 * B)) * (1 / B) *
            thetaLikelihoodSixthScoreRayTransformPolynomial (A / B) (15 / 8 + 3 * d)) =
        (Real.exp (-(9 / 2 : ℝ)) * Real.exp (-(3 * B))) *
          (16 * thetaLikelihoodSixthScoreShift (15 / 8 + 3 * d) +
            18 * (1 / B) * thetaLikelihoodSixthScoreRayTransformPolynomial
              (A / B) (15 / 8 + 3 * d)) by ring]
    rw [hextract, hAeq, hBeq]
    rfl
  have hexpd : Real.exp (-(3 * d)) ≤ 1 - 3 * d + (3 * d) ^ (2 : ℕ) / 2 :=
    exp_neg_le_quadratic (by positivity)
  have hExp : Real.exp (-3 * A) <
      (1 / 52800 : ℝ) * (1 - 3 * d + (3 * d) ^ (2 : ℕ) / 2) := by
    calc
      Real.exp (-3 * A) = Real.exp (-(87 / 8 : ℝ)) * Real.exp (-(3 * d)) := by
        rw [← Real.exp_add, hAeq]
        congr 1
        ring
      _ < (1 / 52800 : ℝ) * Real.exp (-(3 * d)) := by
        gcongr
        exact exp_neg_eightySevenEighths_lt_oneOverFiftyTwoThousandEightHundred
      _ ≤ (1 / 52800 : ℝ) * (1 - 3 * d + (3 * d) ^ (2 : ℕ) / 2) := by gcongr
  have hpolypos : 0 < thetaCuspLikelihoodSixthScale29Over8DominantPolynomial d := by
    have hBd : 0 < 17 / 8 + d := by linarith
    dsimp [thetaCuspLikelihoodSixthScale29Over8DominantPolynomial,
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
    _ < ((1 / 52800 : ℝ) * (1 - 3 * d + (3 * d) ^ (2 : ℕ) / 2)) *
        thetaCuspLikelihoodSixthScale29Over8DominantPolynomial d := by gcongr
    _ < 282 - 480 * d := by
      simpa only [mul_assoc] using
        thetaCuspLikelihoodSixthScale29Over8DominantPolynomial_lt hd hdhi
    _ = 282 - 480 * (A - 29 / 8) := by rfl

/-- Dominant plus stable sixth-score mass is below `565/2 - 480d`. -/
theorem integral_thetaLikelihoodSixthScore_lt_scale29Over8_affine
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (29 / 8 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 175 / 48) :
    (∫ t : ℝ,
        thetaLikelihoodSixthScore (thetaCuspSingleAtomReflectionScale 1 x * t) *
          Real.exp (-(thetaCuspLikelihoodCoordinate x * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure) <
      565 / 2 - 480 * (thetaCuspSingleAtomReflectionScale 1 x - 29 / 8) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hd := thetaCuspLikelihoodDominantAtomSixthScoreMass_lt_scale29Over8_affine
    A (by simpa only [A] using hAlo) (by simpa only [A] using hAhi) hBA
  have hs := tsum_thetaCuspLikelihoodStableAtomSixthScoreMass_lt_oneHalf_of_29Over8_le
    (by simpa only [A] using hAlo) hBA
  rw [thetaCuspLikelihoodSixthScoreIntegral_eq_dominant_add_stable hx]
  dsimp only [A, B] at hd hs ⊢
  nlinarith

/-- Affine logarithmic sixth-jet ceiling on the scale-`29/8` chamber. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetSix_lt_scale29Over8_affine
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (29 / 8 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 175 / 48) :
    thetaCuspLikelihoodSourceLogPartitionJetSix x <
      (40076 / 625 : ℝ) *
        (565 / 2 - 480 * (thetaCuspSingleAtomReflectionScale 1 x - 29 / 8)) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let massBudget := 565 / 2 - 480 * (A - 29 / 8)
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
      integral_thetaLikelihoodSixthScore_lt_scale29Over8_affine hx hAlo hAhi
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
    thetaCuspLikelihoodSourceLogPartitionJetSix_lt_tenThousandNineteenTenThousandths_ordinary_of_29Over8_le
      hx hAlo
  dsimp only [massBudget, A] at hordinary ⊢
  nlinarith

/-- Weight-coordinate form of the scale-`29/8` sixth ceiling. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetSix_lt_scale29Over8_affine_weight
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (29 / 8 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 175 / 48) :
    thetaCuspLikelihoodSourceLogPartitionJetSix x <
      (40076 / 625 : ℝ) *
        (2605 / 2 - 480 * thetaCuspBornWittenWeight 1 x) := by
  have hscale : thetaCuspSingleAtomReflectionScale 1 x =
      thetaCuspBornWittenWeight 1 x + 3 / 2 := by
    dsimp only [thetaCuspSingleAtomReflectionScale]
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have h := thetaCuspLikelihoodSourceLogPartitionJetSix_lt_scale29Over8_affine
    hx hAlo hAhi
  rw [hscale] at h
  convert h using 1
  all_goals ring

end

end RHTower
