import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthScaleThreeHundredFiftyNineNinetySixthsAffineBound
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthStableTowerScaleOneHundredSeventyNineFortyEighthsBound

/-!
# Scale-179/48 affine upper bound for sixth theta likelihood jet

Exact moving first-atom ratios and the scale-local stable-tower bound `<1` give dominant mass
`<237-432d`, complete mass `<238-432d`, and `J₆ < (1656/25)(238-432d)` on
`179/48 ≤ A ≤ 15/4`.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Exact rational score factor after extracting `exp(-3A)` at scale `179/48`. -/
def thetaCuspLikelihoodSixthScale179Over48DominantPolynomial (d : ℝ) : ℝ :=
  16 * thetaLikelihoodSixthScoreShift (35 / 16 + 3 * d) +
    18 * (1 / (107 / 48 + d)) *
      thetaLikelihoodSixthScoreRayTransformPolynomial
        ((179 / 48 + d) / (107 / 48 + d)) (35 / 16 + 3 * d)

/-- Cleared degree-fifteen certificate for dominant budget. -/
theorem thetaCuspLikelihoodSixthScale179Over48DominantPolynomial_lt
    {d : ℝ} (hd : 0 ≤ d) (hdhi : d ≤ 1 / 48) :
    (1 / 72000 : ℝ) * (1 - 3 * d + (3 * d) ^ 2 / 2) *
        thetaCuspLikelihoodSixthScale179Over48DominantPolynomial d <
      237 - 432 * d := by
  have hB : 0 < 107 / 48 + d := by linarith
  have hmul : (107 / 48 + d) ^ 7 *
      ((1 / 72000 : ℝ) * (1 - 3 * d + (3 * d) ^ 2 / 2) *
        thetaCuspLikelihoodSixthScale179Over48DominantPolynomial d) <
      (107 / 48 + d) ^ 7 * (237 - 432 * d) := by
    dsimp [thetaCuspLikelihoodSixthScale179Over48DominantPolynomial,
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
    have hd2 : d ^ 2 ≤ (1 / 48 : ℝ) ^ 2 := pow_le_pow_left₀ hd hdhi 2
    have hd3 : d ^ 3 ≤ (1 / 48 : ℝ) ^ 3 := pow_le_pow_left₀ hd hdhi 3
    have hd4 : d ^ 4 ≤ (1 / 48 : ℝ) ^ 4 := pow_le_pow_left₀ hd hdhi 4
    have hd5 : d ^ 5 ≤ (1 / 48 : ℝ) ^ 5 := pow_le_pow_left₀ hd hdhi 5
    have hd6 : d ^ 6 ≤ (1 / 48 : ℝ) ^ 6 := pow_le_pow_left₀ hd hdhi 6
    have hd7 : d ^ 7 ≤ (1 / 48 : ℝ) ^ 7 := pow_le_pow_left₀ hd hdhi 7
    have hd8 : d ^ 8 ≤ (1 / 48 : ℝ) ^ 8 := pow_le_pow_left₀ hd hdhi 8
    have hd9 : d ^ 9 ≤ (1 / 48 : ℝ) ^ 9 := pow_le_pow_left₀ hd hdhi 9
    have hd10 : d ^ 10 ≤ (1 / 48 : ℝ) ^ 10 := pow_le_pow_left₀ hd hdhi 10
    have hd11 : d ^ 11 ≤ (1 / 48 : ℝ) ^ 11 := pow_le_pow_left₀ hd hdhi 11
    have hd12 : d ^ 12 ≤ (1 / 48 : ℝ) ^ 12 := pow_le_pow_left₀ hd hdhi 12
    have hd13 : d ^ 13 ≤ (1 / 48 : ℝ) ^ 13 := pow_le_pow_left₀ hd hdhi 13
    have hd14 : d ^ 14 ≤ (1 / 48 : ℝ) ^ 14 := pow_le_pow_left₀ hd hdhi 14
    have hd15 : d ^ 15 ≤ (1 / 48 : ℝ) ^ 15 := pow_le_pow_left₀ hd hdhi 15
    norm_num at hd2 hd3 hd4 hd5 hd6 hd7 hd8 hd9 hd10 hd11 hd12 hd13 hd14 hd15 ⊢
    nlinarith
  nlinarith [pow_pos hB 7]

/-- Rational exponential upper enclosure at scale `179/48`. -/
theorem exp_neg_oneHundredSeventyNineSixteenths_lt_oneSeventyTwoThousand :
    Real.exp (-(179 / 16 : ℝ)) < (1 / 72000 : ℝ) := by
  have hpow : Real.exp (-1) ^ 11 < (0.3678794412 : ℝ) ^ 11 :=
    pow_lt_pow_left₀ Real.exp_neg_one_lt_d9 (Real.exp_pos (-1)).le (by norm_num)
  have hthree : Real.exp (-(3 / 16 : ℝ)) < (83 / 100 : ℝ) := by
    have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 16) 3
    have hb : (100 / 83 : ℝ) < Real.exp (3 / 16) := by
      calc
        (100 / 83 : ℝ) <
            ∑ k ∈ Finset.range 3, (3 / 16 : ℝ) ^ k / k.factorial := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
        _ ≤ Real.exp (3 / 16) := he
    have hprod : Real.exp (-(3 / 16 : ℝ)) * Real.exp (3 / 16 : ℝ) = 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [Real.exp_pos (-(3 / 16 : ℝ))]
  rw [show (-(179 / 16 : ℝ)) = -11 + -(3 / 16 : ℝ) by norm_num,
    Real.exp_add,
    show Real.exp (-11) = Real.exp (-1) ^ 11 by
      rw [show (-11 : ℝ) = (11 : ℕ) * (-1 : ℝ) by norm_num,
        Real.exp_nat_mul]]
  nlinarith [Real.exp_pos (-1), Real.exp_pos (-(3 / 16 : ℝ)),
    show (0.3678794412 : ℝ) ^ 11 * (83 / 100 : ℝ) < 1 / 72000 by norm_num]

/-- Dominant first atom-ray mass obeys `237 - 432d`. -/
theorem thetaCuspLikelihoodDominantAtomSixthScoreMass_lt_scale179Over48_affine
    (A : ℝ) {B : ℝ} (hAlo : (179 / 48 : ℝ) ≤ A) (hAhi : A ≤ 15 / 4)
    (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodDominantAtomSixthScoreMass A B <
      237 - 432 * (A - 179 / 48) := by
  have hB : 0 < B := by rw [hBA]; linarith
  let d := A - 179 / 48
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hdhi : d ≤ 1 / 48 := by dsimp only [d]; linarith
  have hAeq : A = 179 / 48 + d := by dsimp only [d]; ring
  have hBeq : B = 107 / 48 + d := by rw [hBA, hAeq]; ring
  have hy : 3 * A - 9 = 35 / 16 + 3 * d := by rw [hAeq]; ring
  have hextract :
      Real.exp (-(9 / 2 : ℝ)) * Real.exp (-(3 * B)) = Real.exp (-3 * A) := by
    rw [← Real.exp_add]
    congr 1
    rw [hBA]
    ring
  have hmassEq : thetaCuspLikelihoodDominantAtomSixthScoreMass A B =
      Real.exp (-3 * A) * thetaCuspLikelihoodSixthScale179Over48DominantPolynomial d := by
    rw [thetaCuspLikelihoodDominantAtomSixthScoreMass_eq A hB,
      thetaLikelihoodSixthScore_eq_shiftNine, hy]
    rw [show Real.exp (-(3 * B)) / B = Real.exp (-(3 * B)) * (1 / B) by ring]
    rw [show 16 * Real.exp (-(9 / 2 : ℝ)) *
          (thetaLikelihoodSixthScoreShift (35 / 16 + 3 * d) * Real.exp (-(3 * B))) +
        18 * Real.exp (-(9 / 2 : ℝ)) *
          (Real.exp (-(3 * B)) * (1 / B) *
            thetaLikelihoodSixthScoreRayTransformPolynomial (A / B) (35 / 16 + 3 * d)) =
        (Real.exp (-(9 / 2 : ℝ)) * Real.exp (-(3 * B))) *
          (16 * thetaLikelihoodSixthScoreShift (35 / 16 + 3 * d) +
            18 * (1 / B) *
              thetaLikelihoodSixthScoreRayTransformPolynomial
                (A / B) (35 / 16 + 3 * d)) by ring]
    rw [hextract, hAeq, hBeq]
    rfl
  have hexpd : Real.exp (-(3 * d)) ≤ 1 - 3 * d + (3 * d) ^ 2 / 2 :=
    exp_neg_le_quadratic (by positivity)
  have hExp : Real.exp (-3 * A) <
      (1 / 72000 : ℝ) * (1 - 3 * d + (3 * d) ^ 2 / 2) := by
    calc
      Real.exp (-3 * A) = Real.exp (-(179 / 16 : ℝ)) * Real.exp (-(3 * d)) := by
        rw [← Real.exp_add, hAeq]
        congr 1
        ring
      _ < (1 / 72000 : ℝ) * Real.exp (-(3 * d)) := by
        gcongr
        exact exp_neg_oneHundredSeventyNineSixteenths_lt_oneSeventyTwoThousand
      _ ≤ (1 / 72000 : ℝ) * (1 - 3 * d + (3 * d) ^ 2 / 2) := by gcongr
  have hpolypos : 0 < thetaCuspLikelihoodSixthScale179Over48DominantPolynomial d := by
    have hBd : 0 < 107 / 48 + d := by linarith
    dsimp [thetaCuspLikelihoodSixthScale179Over48DominantPolynomial,
      thetaLikelihoodSixthScoreRayTransformPolynomial,
      thetaLikelihoodSixthScoreShift, thetaLikelihoodSixthScoreShiftDerivOne,
      thetaLikelihoodSixthScoreShiftDerivTwo,
      thetaLikelihoodSixthScoreShiftDerivThree,
      thetaLikelihoodSixthScoreShiftDerivFour,
      thetaLikelihoodSixthScoreShiftDerivFive,
      thetaLikelihoodSixthScoreShiftDerivSix]
    positivity
  have hpoly := thetaCuspLikelihoodSixthScale179Over48DominantPolynomial_lt hd hdhi
  rw [hmassEq]
  exact (mul_lt_mul_of_pos_right hExp hpolypos).trans hpoly

/-- Dominant plus stable sixth-score mass is below `238 - 432d`. -/
theorem integral_thetaLikelihoodSixthScore_lt_scale179Over48_affine
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (179 / 48 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 15 / 4) :
    (∫ t : ℝ,
        thetaLikelihoodSixthScore (thetaCuspSingleAtomReflectionScale 1 x * t) *
          Real.exp (-(thetaCuspLikelihoodCoordinate x * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure) <
      238 - 432 * (thetaCuspSingleAtomReflectionScale 1 x - 179 / 48) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hd := thetaCuspLikelihoodDominantAtomSixthScoreMass_lt_scale179Over48_affine
    A (by simpa only [A] using hAlo) (by simpa only [A] using hAhi) hBA
  have hs := tsum_thetaCuspLikelihoodStableAtomSixthScoreMass_lt_one_of_179Over48_le
    (by simpa only [A] using hAlo) hBA
  rw [thetaCuspLikelihoodSixthScoreIntegral_eq_dominant_add_stable hx]
  dsimp only [A, B] at hd hs ⊢
  nlinarith

/-- Affine logarithmic sixth-jet ceiling on new chamber. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetSix_lt_scale179Over48_affine
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (179 / 48 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 15 / 4) :
    thetaCuspLikelihoodSourceLogPartitionJetSix x <
      (1656 / 25 : ℝ) *
        (238 - 432 * (thetaCuspSingleAtomReflectionScale 1 x - 179 / 48)) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let massBudget := 238 - 432 * (A - 179 / 48)
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
      integral_thetaLikelihoodSixthScore_lt_scale179Over48_affine hx hAlo hAhi
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
    thetaCuspLikelihoodSourceLogPartitionJetSix_lt_twoHundredSevenTwoHundredths_ordinary hx
  dsimp only [massBudget, A] at hordinary ⊢
  nlinarith

/-- Weight-coordinate form: `J₆ < (1656/25)(1201 - 432q)`. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetSix_lt_scale179Over48_affine_weight
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (179 / 48 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 15 / 4) :
    thetaCuspLikelihoodSourceLogPartitionJetSix x <
      (1656 / 25 : ℝ) * (1201 - 432 * thetaCuspBornWittenWeight 1 x) := by
  have hscale : thetaCuspSingleAtomReflectionScale 1 x =
      thetaCuspBornWittenWeight 1 x + 3 / 2 := by
    dsimp only [thetaCuspSingleAtomReflectionScale]
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ 2 = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have h := thetaCuspLikelihoodSourceLogPartitionJetSix_lt_scale179Over48_affine
    hx hAlo hAhi
  rw [hscale] at h
  convert h using 1 <;> ring

end
end RHTower
