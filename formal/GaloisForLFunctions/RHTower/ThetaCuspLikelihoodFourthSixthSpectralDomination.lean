import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthCompleteSpectralBound

open MeasureTheory Set

/-!
# Fourth--sixth spectral domination for the theta likelihood

The fourth logarithmic likelihood jet cannot be bounded sharply by independent derivative
majorants.  The fixed spectral measure exposes the missing cancellation: on its support, the
literal fourth source score is dominated by `3/20` of the sixth score.  After the small nonlinear
logarithmic correction is paid, the fourth log jet is less than `1/25` of the ordinary sixth jet.

The same file sharpens the dominant sixth ray Taylor envelope from `1000000` to `950000` and turns
that coefficient gain into the rational bounds `ordinary₆ < 60800`, `log₆ < 63232`, and
`log₄ < 2432`.  All estimates are source-only and unconditional.
-/

namespace RHTower

noncomputable section

/-- Fourth ordinary source score in the intrinsic spectral variable. -/
def thetaLikelihoodFourthScore (z : ℝ) : ℝ :=
  z ^ 4 - 6 * z ^ 3 + 7 * z ^ 2 - z

/-- At the physical support edge, two fifths of the leading fourth monomial survive. -/
theorem two_fifths_mul_pow_four_le_thetaLikelihoodFourthScore
    {z : ℝ} (hz : (47 / 5 : ℝ) ≤ z) :
    (2 / 5 : ℝ) * z ^ 4 ≤ thetaLikelihoodFourthScore z := by
  let y := z - 47 / 5
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  have hy3 : 0 ≤ y ^ 3 := by positivity
  have hy4 : 0 ≤ y ^ 4 := by positivity
  rw [show z = 47 / 5 + y by dsimp [y]; ring]
  dsimp [thetaLikelihoodFourthScore]
  ring_nf
  nlinarith

/-- Pointwise score bridge on the exact higher-likelihood support. -/
theorem thetaLikelihoodFourthScore_le_threeTwentieths_sixthScore
    {z : ℝ} (hz : (47 / 5 : ℝ) ≤ z) :
    thetaLikelihoodFourthScore z ≤
      (3 / 20 : ℝ) * thetaLikelihoodSixthScore z := by
  let y := z - 47 / 5
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  have hy3 : 0 ≤ y ^ 3 := by positivity
  have hy4 : 0 ≤ y ^ 4 := by positivity
  have hy5 : 0 ≤ y ^ 5 := by positivity
  have hy6 : 0 ≤ y ^ 6 := by positivity
  rw [show z = 47 / 5 + y by dsimp [y]; ring]
  dsimp [thetaLikelihoodFourthScore, thetaLikelihoodSixthScore]
  ring_nf
  nlinarith

/-- Normalized one-particle ordinary fourth score of the higher theta likelihood source. -/
def thetaCuspLikelihoodSourceOrdinaryJetFour (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  16 * (A ^ 4 * thetaCuspLikelihoodNormalizedMoment B 4 -
    6 * A ^ 3 * thetaCuspLikelihoodNormalizedMoment B 3 +
    7 * A ^ 2 * thetaCuspLikelihoodNormalizedMoment B 2 -
    A * thetaCuspLikelihoodMean B)

private theorem integrable_thetaLikelihoodFourthScore_tilted
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ => thetaLikelihoodFourthScore (A * t))
      (thetaCuspHigherLikelihoodTiltedMeasure B) := by
  have h4 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 4 hB).const_mul (A ^ 4)
  have h3 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 3 hB).const_mul (6 * A ^ 3)
  have h2 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 2 hB).const_mul (7 * A ^ 2)
  have h1 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 1 hB).const_mul A
  convert (((h4.sub h3).add h2).sub h1) using 1
  funext t
  dsimp [thetaLikelihoodFourthScore]
  ring

private theorem integrable_thetaLikelihoodSixthScore_tilted
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ => thetaLikelihoodSixthScore (A * t))
      (thetaCuspHigherLikelihoodTiltedMeasure B) := by
  have h6 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 6 hB).const_mul (A ^ 6)
  have h5 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 5 hB).const_mul (15 * A ^ 5)
  have h4 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 4 hB).const_mul (65 * A ^ 4)
  have h3 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 3 hB).const_mul (90 * A ^ 3)
  have h2 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 2 hB).const_mul (31 * A ^ 2)
  have h1 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 1 hB).const_mul A
  convert ((((h6.sub h5).add h4).sub h3).add h2).sub h1 using 1
  funext t
  dsimp [thetaLikelihoodSixthScore]
  ring

private theorem integral_thetaLikelihoodFourthScore_tilted_eq
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ, thetaLikelihoodFourthScore (A * t)
      ∂thetaCuspHigherLikelihoodTiltedMeasure B) =
      A ^ 4 * thetaCuspHigherLikelihoodSpectralMoment B 4 -
        6 * A ^ 3 * thetaCuspHigherLikelihoodSpectralMoment B 3 +
        7 * A ^ 2 * thetaCuspHigherLikelihoodSpectralMoment B 2 -
        A * thetaCuspHigherLikelihoodSpectralMoment B 1 := by
  have h4 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 4 hB).const_mul (A ^ 4)
  have h3 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 3 hB).const_mul (6 * A ^ 3)
  have h2 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 2 hB).const_mul (7 * A ^ 2)
  have h1 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 1 hB).const_mul A
  let f4 : ℝ → ℝ := fun t => A ^ 4 * t ^ 4
  let f3 : ℝ → ℝ := fun t => (6 * A ^ 3) * t ^ 3
  let f2 : ℝ → ℝ := fun t => (7 * A ^ 2) * t ^ 2
  let f1 : ℝ → ℝ := fun t => A * t ^ 1
  rw [show (fun t : ℝ => thetaLikelihoodFourthScore (A * t)) =
      ((f4 - f3) + f2) - f1 by
    funext t
    dsimp [thetaLikelihoodFourthScore, f4, f3, f2, f1]
    ring]
  rw [integral_sub' ((h4.sub h3).add h2) h1,
    integral_add' (h4.sub h3) h2, integral_sub' h4 h3]
  simp only [integral_const_mul]
  rfl

private theorem integral_thetaLikelihoodSixthScore_tilted_eq
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ, thetaLikelihoodSixthScore (A * t)
      ∂thetaCuspHigherLikelihoodTiltedMeasure B) =
      A ^ 6 * thetaCuspHigherLikelihoodSpectralMoment B 6 -
        15 * A ^ 5 * thetaCuspHigherLikelihoodSpectralMoment B 5 +
        65 * A ^ 4 * thetaCuspHigherLikelihoodSpectralMoment B 4 -
        90 * A ^ 3 * thetaCuspHigherLikelihoodSpectralMoment B 3 +
        31 * A ^ 2 * thetaCuspHigherLikelihoodSpectralMoment B 2 -
        A * thetaCuspHigherLikelihoodSpectralMoment B 1 := by
  have h6 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 6 hB).const_mul (A ^ 6)
  have h5 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 5 hB).const_mul (15 * A ^ 5)
  have h4 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 4 hB).const_mul (65 * A ^ 4)
  have h3 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 3 hB).const_mul (90 * A ^ 3)
  have h2 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 2 hB).const_mul (31 * A ^ 2)
  have h1 := (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 1 hB).const_mul A
  let f6 : ℝ → ℝ := fun t => A ^ 6 * t ^ 6
  let f5 : ℝ → ℝ := fun t => (15 * A ^ 5) * t ^ 5
  let f4 : ℝ → ℝ := fun t => (65 * A ^ 4) * t ^ 4
  let f3 : ℝ → ℝ := fun t => (90 * A ^ 3) * t ^ 3
  let f2 : ℝ → ℝ := fun t => (31 * A ^ 2) * t ^ 2
  let f1 : ℝ → ℝ := fun t => A * t ^ 1
  rw [show (fun t : ℝ => thetaLikelihoodSixthScore (A * t)) =
      ((((f6 - f5) + f4) - f3) + f2) - f1 by
    funext t
    dsimp [thetaLikelihoodSixthScore, f6, f5, f4, f3, f2, f1]
    ring]
  rw [integral_sub' ((((h6.sub h5).add h4).sub h3).add h2) h1,
    integral_add' (((h6.sub h5).add h4).sub h3) h2,
    integral_sub' ((h6.sub h5).add h4) h3,
    integral_add' (h6.sub h5) h4, integral_sub' h6 h5]
  simp only [integral_const_mul]
  rfl

private theorem fortySevenFifteenths_lt_thetaCuspFirstReflectionScale
    {x : ℝ} (hx : 0 ≤ x) :
    (47 / 15 : ℝ) < thetaCuspSingleAtomReflectionScale 1 x := by
  have hpi := Real.pi_gt_d2
  norm_num at hpi
  have hscale : Real.pi ≤ thetaCuspSingleAtomReflectionScale 1 x := by
    dsimp [thetaCuspSingleAtomReflectionScale]
    norm_num
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    nlinarith [Real.pi_pos]
  linarith

/-- The ordinary fourth likelihood score is at most `3/80` of the ordinary sixth score. -/
theorem thetaCuspLikelihoodSourceOrdinaryJetFour_le_threeEightieths_six
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodSourceOrdinaryJetFour x ≤
      (3 / 80 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetSix x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hA : (47 / 15 : ℝ) < A := by
    simpa only [A] using fortySevenFifteenths_lt_thetaCuspFirstReflectionScale hx
  have hI4 := integrable_thetaLikelihoodFourthScore_tilted A hB
  have hI6 := integrable_thetaLikelihoodSixthScore_tilted A hB
  have hpoint : ∀ᵐ t ∂thetaCuspHigherLikelihoodTiltedMeasure B,
      thetaLikelihoodFourthScore (A * t) ≤
        (3 / 20 : ℝ) * thetaLikelihoodSixthScore (A * t) := by
    filter_upwards [ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure B] with t ht
    apply thetaLikelihoodFourthScore_le_threeTwentieths_sixthScore
    nlinarith [mul_lt_mul_of_pos_right hA (show 0 < t by linarith)]
  have hscaledI6 : Integrable
      (fun t : ℝ => (3 / 20 : ℝ) * thetaLikelihoodSixthScore (A * t))
      (thetaCuspHigherLikelihoodTiltedMeasure B) := hI6.const_mul _
  have hint := integral_mono_ae hI4 hscaledI6 hpoint
  rw [integral_const_mul] at hint
  rw [integral_thetaLikelihoodFourthScore_tilted_eq A hB,
    integral_thetaLikelihoodSixthScore_tilted_eq A hB] at hint
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hcoeff : 0 ≤ 16 / P := div_nonneg (by norm_num) hP.le
  have hscaled := mul_le_mul_of_nonneg_left hint hcoeff
  calc
    thetaCuspLikelihoodSourceOrdinaryJetFour x =
        (16 / P) *
          (A ^ 4 * thetaCuspHigherLikelihoodSpectralMoment B 4 -
            6 * A ^ 3 * thetaCuspHigherLikelihoodSpectralMoment B 3 +
            7 * A ^ 2 * thetaCuspHigherLikelihoodSpectralMoment B 2 -
            A * thetaCuspHigherLikelihoodSpectralMoment B 1) := by
      dsimp only [thetaCuspLikelihoodSourceOrdinaryJetFour, A, B]
      unfold thetaCuspLikelihoodNormalizedMoment thetaCuspLikelihoodMean
      dsimp only [P]
      field_simp [hP.ne']
      ring
    _ ≤ (16 / P) * ((3 / 20 : ℝ) *
          (A ^ 6 * thetaCuspHigherLikelihoodSpectralMoment B 6 -
            15 * A ^ 5 * thetaCuspHigherLikelihoodSpectralMoment B 5 +
            65 * A ^ 4 * thetaCuspHigherLikelihoodSpectralMoment B 4 -
            90 * A ^ 3 * thetaCuspHigherLikelihoodSpectralMoment B 3 +
            31 * A ^ 2 * thetaCuspHigherLikelihoodSpectralMoment B 2 -
            A * thetaCuspHigherLikelihoodSpectralMoment B 1)) := hscaled
    _ = (3 / 80 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetSix x := by
      dsimp only [thetaCuspLikelihoodSourceOrdinaryJetSix, A, B]
      unfold thetaCuspLikelihoodNormalizedMoment thetaCuspLikelihoodMean
      dsimp only [P]
      field_simp [hP.ne']
      ring

/-- The ordinary fourth score retains two fifths of its leading spectral moment. -/
theorem two_fifths_le_thetaCuspLikelihoodSourceOrdinaryJetFour
    {x : ℝ} (hx : 0 ≤ x) :
    (32 / 5 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 4 *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 4 ≤
      thetaCuspLikelihoodSourceOrdinaryJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hA : (47 / 15 : ℝ) < A := by
    simpa only [A] using fortySevenFifteenths_lt_thetaCuspFirstReflectionScale hx
  have hI4 := integrable_thetaLikelihoodFourthScore_tilted A hB
  have hlead : Integrable (fun t : ℝ =>
      (2 / 5 : ℝ) * A ^ 4 * t ^ 4)
      (thetaCuspHigherLikelihoodTiltedMeasure B) :=
    (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 4 hB).const_mul _
  have hpoint : ∀ᵐ t ∂thetaCuspHigherLikelihoodTiltedMeasure B,
      (2 / 5 : ℝ) * A ^ 4 * t ^ 4 ≤ thetaLikelihoodFourthScore (A * t) := by
    filter_upwards [ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure B] with t ht
    have hAt : (47 / 5 : ℝ) ≤ A * t := by
      nlinarith [mul_lt_mul_of_pos_right hA (show 0 < t by linarith)]
    have h := two_fifths_mul_pow_four_le_thetaLikelihoodFourthScore hAt
    convert h using 1
    all_goals ring
  have hint := integral_mono_ae hlead hI4 hpoint
  rw [integral_const_mul,
    show (∫ t : ℝ, t ^ 4 ∂thetaCuspHigherLikelihoodTiltedMeasure B) =
      thetaCuspHigherLikelihoodSpectralMoment B 4 by rfl,
    integral_thetaLikelihoodFourthScore_tilted_eq A hB] at hint
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hcoeff : 0 ≤ 16 / P := div_nonneg (by norm_num) hP.le
  have hscaled := mul_le_mul_of_nonneg_left hint hcoeff
  calc
    (32 / 5 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 4 *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 4 =
      (16 / P) * ((2 / 5 : ℝ) * A ^ 4 *
        thetaCuspHigherLikelihoodSpectralMoment B 4) := by
          dsimp only [A, B]
          unfold thetaCuspLikelihoodNormalizedMoment
          dsimp only [P]
          field_simp [hP.ne']
          ring
    _ ≤ (16 / P) *
        (A ^ 4 * thetaCuspHigherLikelihoodSpectralMoment B 4 -
          6 * A ^ 3 * thetaCuspHigherLikelihoodSpectralMoment B 3 +
          7 * A ^ 2 * thetaCuspHigherLikelihoodSpectralMoment B 2 -
          A * thetaCuspHigherLikelihoodSpectralMoment B 1) := hscaled
    _ = thetaCuspLikelihoodSourceOrdinaryJetFour x := by
      dsimp only [thetaCuspLikelihoodSourceOrdinaryJetFour, A, B]
      unfold thetaCuspLikelihoodNormalizedMoment thetaCuspLikelihoodMean
      dsimp only [P]
      field_simp [hP.ne']
      ring

/-- The logarithmic fourth jet differs from its one-particle score by less than one per mille. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetFour_lt_ordinary
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodSourceLogPartitionJetFour x <
      (1001 / 1000 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let p := thetaCuspLikelihoodTailProbability B
  let e1 := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  let e4 := thetaCuspLikelihoodNormalizedMoment B 4
  let b1 := 2 * A * e1
  let b2 := 4 * (A ^ 2 * e2 - A * e1)
  let b3 := 8 * (A ^ 3 * e3 - 3 * A ^ 2 * e2 + A * e1)
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
    simpa only [e2, e3] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
  have he34 : 3 * e3 ≤ e4 := by
    simpa only [e3, e4] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 3
  have he3 : 0 < e3 := lt_of_lt_of_le (mul_pos (by norm_num) he2) he23
  have he4 : 0 < e4 := lt_of_lt_of_le (mul_pos (by norm_num) he3) he34
  have hpSmall : 400 * p < 1 := by
    simpa only [B, p] using
      four_hundred_mul_thetaCuspLikelihoodTailProbability_coordinate_lt_one hx
  have hp : 0 < p := by
    have h22 := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 2 2
    have h22' : e2 ^ 2 ≤ p * e4 := by
      simpa only [B, p, e2, e4, show 2 + 2 = 4 by norm_num, pow_two] using h22
    nlinarith [sq_pos_of_pos he2]
  have h11 : e1 ^ 2 ≤ p * e2 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 1 1
    simpa only [B, p, e1, e2, thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 1 = 2 by norm_num, pow_two] using h
  have h22 : e2 ^ 2 ≤ p * e4 := by
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
  have hb2Upper : b2 ≤ 4 * A ^ 2 * e2 := by
    dsimp only [b2]
    nlinarith [mul_pos hA0 he1]
  have hAe3 : 3 * e2 < A * e3 := by
    have hmul := mul_lt_mul_of_pos_right hA he3
    nlinarith
  have hb3 : 0 < b3 := by
    have hmul := mul_lt_mul_of_pos_left hAe3 (pow_pos hA0 2)
    dsimp only [b3]
    nlinarith [mul_pos hA0 he1]
  have hb4Lower : (32 / 5 : ℝ) * A ^ 4 * e4 ≤ b4 := by
    simpa only [A, B, e4, b4] using
      two_fifths_le_thetaCuspLikelihoodSourceOrdinaryJetFour hx
  have hb4 : 0 < b4 := lt_of_lt_of_le (by positivity) hb4Lower
  have hb1SqB2 : b1 ^ 2 * b2 ≤ 16 * A ^ 4 * (e1 ^ 2 * e2) := by
    calc
      b1 ^ 2 * b2 ≤ (2 * A * e1) ^ 2 * (4 * A ^ 2 * e2) := by gcongr
      _ = 16 * A ^ 4 * (e1 ^ 2 * e2) := by ring
  have he112 : e1 ^ 2 * e2 ≤ p ^ 2 * e4 := by
    calc
      e1 ^ 2 * e2 ≤ (p * e2) * e2 :=
        mul_le_mul_of_nonneg_right h11 he2.le
      _ = p * e2 ^ 2 := by ring
      _ ≤ p * (p * e4) := mul_le_mul_of_nonneg_left h22 hp.le
      _ = p ^ 2 * e4 := by ring
  have hparticle : 12 * b1 ^ 2 * b2 ≤ 30 * p ^ 2 * b4 := by
    have h1 := mul_le_mul_of_nonneg_left hb1SqB2 (by norm_num : (0 : ℝ) ≤ 12)
    have h2 := mul_le_mul_of_nonneg_left he112
      (show 0 ≤ 192 * A ^ 4 by positivity)
    have h3 := mul_le_mul_of_nonneg_left hb4Lower
      (show 0 ≤ 30 * p ^ 2 by positivity)
    nlinarith
  have hp2 : p ^ 2 < (1 / 400 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ (by nlinarith : p < (1 / 400 : ℝ)) hp.le (by norm_num)
  have hbudget : 30 * p ^ 2 < (1 / 5000 : ℝ) := by
    norm_num at hp2 ⊢
    nlinarith
  have hparticleSmall : 12 * b1 ^ 2 * b2 < (1 / 5000 : ℝ) * b4 :=
    lt_of_le_of_lt hparticle (mul_lt_mul_of_pos_right hbudget hb4)
  have hdecomp :
      thetaCuspLikelihoodSourceLogPartitionJetFour x =
        b4 - 4 * b1 * b3 - 3 * b2 ^ 2 + 12 * b1 ^ 2 * b2 - 6 * b1 ^ 4 := by
    dsimp only [b1, b2, b3, b4, A, B, e1, e2, e3, e4]
    unfold thetaCuspLikelihoodSourceOrdinaryJetFour
      thetaCuspLikelihoodSourceLogPartitionJetFour thetaCuspLikelihoodFourthCumulant
      thetaCuspLikelihoodThirdCumulant
    rw [thetaCuspLikelihoodVariance_eq_normalizedMoment_two_sub_mean_sq]
    unfold thetaCuspLikelihoodNormalizedMoment thetaCuspLikelihoodMean
    ring
  rw [hdecomp]
  nlinarith [mul_pos hb1 hb3, sq_nonneg b2, pow_pos hb1 4]

/-- Shared-spectrum domination of the fourth logarithmic loss by the sixth ordinary score. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetFour_lt_oneTwentyFifth_six
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodSourceLogPartitionJetFour x <
      (1 / 25 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetSix x := by
  have h4 := thetaCuspLikelihoodSourceLogPartitionJetFour_lt_ordinary hx
  have h46 := thetaCuspLikelihoodSourceOrdinaryJetFour_le_threeEightieths_six hx
  have h6 := thetaCuspLikelihoodSourceOrdinaryJetSix_pos hx
  nlinarith

/-- Sharp complete sixth-score envelope selected by the coefficient-faithful dominant ray. -/
def thetaCuspLikelihoodSixthSharpEnvelope : ℝ :=
  (16 * 50000 + 18 * (25 / 41 : ℝ) * 950000) *
      Real.exp (-(471 / 50 : ℝ)) +
    (10 / 999 : ℝ) * Real.pi ^ 6

theorem thetaCuspLikelihoodSixthScoreIntegral_le_sharpEnvelope
    {x : ℝ} (hx : 0 ≤ x) :
    (∫ t : ℝ,
        thetaLikelihoodSixthScore
            (thetaCuspSingleAtomReflectionScale 1 x * t) *
          Real.exp (-(thetaCuspLikelihoodCoordinate x * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure) ≤
      thetaCuspLikelihoodSixthSharpEnvelope := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hA : Real.pi ≤ A := by
    dsimp [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    nlinarith [Real.pi_pos]
  have hAseam : (157 / 50 : ℝ) ≤ A := by nlinarith [Real.pi_gt_d2]
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hdominant :=
    thetaCuspLikelihoodDominantAtomSixthScoreMass_le_seamEnvelope_sharp A hAseam hBA
  have hstable := tsum_thetaCuspLikelihoodStableAtomSixthScoreMass_le hA hBA
  rw [thetaCuspLikelihoodSixthScoreIntegral_eq_dominant_add_stable hx]
  dsimp only [thetaCuspLikelihoodSixthSharpEnvelope]
  exact add_le_add hdominant hstable

private theorem exp_neg_nine_lt_oneEightThousand :
    Real.exp (-9) < (1 / 8000 : ℝ) := by
  have hpow : Real.exp (-1) ^ 9 < (0.3678794412 : ℝ) ^ 9 :=
    pow_lt_pow_left₀ Real.exp_neg_one_lt_d9 (Real.exp_pos (-1)).le (by norm_num)
  rw [show (-9 : ℝ) = (9 : ℕ) * (-1 : ℝ) by norm_num, Real.exp_nat_mul]
  exact hpow.trans (by norm_num)

private theorem exp_neg_twentyOneFiftieth_lt_twoThirds :
    Real.exp (-(21 / 50 : ℝ)) < (2 / 3 : ℝ) := by
  have hs := Real.sum_le_exp_of_nonneg (show 0 ≤ (21 / 50 : ℝ) by norm_num) 3
  have hexp : (3 / 2 : ℝ) < Real.exp (21 / 50 : ℝ) := by
    norm_num [Finset.sum_range_succ] at hs ⊢
    linarith
  rw [Real.exp_neg]
  rw [inv_lt_iff_one_lt_mul₀ (Real.exp_pos (21 / 50 : ℝ))]
  nlinarith

private theorem exp_neg_471Fiftieth_lt_oneTwelveThousand :
    Real.exp (-(471 / 50 : ℝ)) < (1 / 12000 : ℝ) := by
  rw [show -(471 / 50 : ℝ) = -9 + -(21 / 50 : ℝ) by ring, Real.exp_add]
  have h9 := exp_neg_nine_lt_oneEightThousand
  have h21 := exp_neg_twentyOneFiftieth_lt_twoThirds
  have h9pos := Real.exp_pos (-9)
  have h21pos := Real.exp_pos (-(21 / 50 : ℝ))
  calc
    Real.exp (-9) * Real.exp (-(21 / 50 : ℝ)) <
        (1 / 8000 : ℝ) * Real.exp (-(21 / 50 : ℝ)) :=
      mul_lt_mul_of_pos_right h9 h21pos
    _ < (1 / 8000 : ℝ) * (2 / 3 : ℝ) :=
      mul_lt_mul_of_pos_left h21 (by norm_num)
    _ = (1 / 12000 : ℝ) := by norm_num

/-- Rational closure of the sharp complete score envelope. -/
theorem thetaCuspLikelihoodSixthSharpEnvelope_lt_nineHundredFifty :
    thetaCuspLikelihoodSixthSharpEnvelope < 950 := by
  have he := exp_neg_471Fiftieth_lt_oneTwelveThousand
  have hpi2 : Real.pi ^ 2 < (10 : ℝ) := by
    nlinarith [Real.pi_pos, Real.pi_lt_d4]
  have hpi6 : Real.pi ^ 6 < (1000 : ℝ) := by
    have h := pow_lt_pow_left₀ hpi2 (sq_nonneg Real.pi)
      (by norm_num : (3 : ℕ) ≠ 0)
    calc
      Real.pi ^ 6 = (Real.pi ^ 2) ^ 3 := by ring
      _ < (10 : ℝ) ^ 3 := h
      _ = 1000 := by norm_num
  have hcoeff :
      0 < (16 * 50000 + 18 * (25 / 41 : ℝ) * 950000) := by norm_num
  have hstable : 0 < (10 / 999 : ℝ) := by norm_num
  have h1 := mul_lt_mul_of_pos_left he hcoeff
  have h2 := mul_lt_mul_of_pos_left hpi6 hstable
  dsimp only [thetaCuspLikelihoodSixthSharpEnvelope]
  norm_num at h1 h2 ⊢
  linarith

/-- Uniform ordinary-sixth likelihood budget in rational form. -/
theorem thetaCuspLikelihoodSourceOrdinaryJetSix_lt_sixtyThousandEightHundred
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodSourceOrdinaryJetSix x < 60800 := by
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let C := thetaCuspLikelihoodSixthSharpEnvelope
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hPone : 1 ≤ P := by
    have hzero := thetaCuspHigherLikelihoodSpectralMoment_nonneg (B := B) 0
    change 1 ≤ thetaCuspLikelihoodPartition B
    rw [thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB]
    linarith
  have hcoeff : 0 ≤ 64 / P := div_nonneg (by norm_num) hP.le
  have hcoeffUpper : 64 / P ≤ 64 := by
    apply (div_le_iff₀ hP).2
    nlinarith
  have hC : 0 ≤ C := by
    dsimp [C, thetaCuspLikelihoodSixthSharpEnvelope]
    positivity
  have hmass := thetaCuspLikelihoodSixthScoreIntegral_le_sharpEnvelope hx
  have hC950 : C < 950 := by
    simpa only [C] using thetaCuspLikelihoodSixthSharpEnvelope_lt_nineHundredFifty
  rw [thetaCuspLikelihoodSourceOrdinaryJetSix_eq_spectralIntegral hx]
  change 64 / P * _ < 60800
  calc
    64 / P * _ ≤ 64 / P * C := mul_le_mul_of_nonneg_left hmass hcoeff
    _ ≤ 64 * C := mul_le_mul_of_nonneg_right hcoeffUpper hC
    _ < 64 * 950 := mul_lt_mul_of_pos_left hC950 (by norm_num)
    _ = 60800 := by norm_num

/-- Sharpened uniform logarithmic-sixth likelihood budget from the exact particle-grade ratio. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetSix_lt_sixtyTwoThousandNineHundredTwentyEight
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodSourceLogPartitionJetSix x < 62928 := by
  have hlog :=
    thetaCuspLikelihoodSourceLogPartitionJetSix_lt_twoHundredSevenTwoHundredths_ordinary hx
  have hord :=
    thetaCuspLikelihoodSourceOrdinaryJetSix_lt_sixtyThousandEightHundred hx
  nlinarith

/-- Compatibility form of the earlier uniform logarithmic-sixth budget. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetSix_lt_sixtyThreeThousandTwoHundredThirtyTwo
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodSourceLogPartitionJetSix x < 63232 :=
  (thetaCuspLikelihoodSourceLogPartitionJetSix_lt_sixtyTwoThousandNineHundredTwentyEight hx).trans
    (by norm_num)

/-- Uniform logarithmic-fourth likelihood budget from the shared fourth--sixth spectrum. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetFour_lt_twoThousandFourHundredThirtyTwo
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodSourceLogPartitionJetFour x < 2432 := by
  have h46 := thetaCuspLikelihoodSourceLogPartitionJetFour_lt_oneTwentyFifth_six hx
  have h6 := thetaCuspLikelihoodSourceOrdinaryJetSix_lt_sixtyThousandEightHundred hx
  nlinarith

set_option maxHeartbeats 800000 in
/-- Quantitative lower orientation: the literal fourth log jet retains more than nineteen
twentieths of its ordinary one-particle score.  The only Bell losses are controlled by the
uniform tail probability `p < 1/400` and normalized moment-product inequalities. -/
theorem nineteenTwentieths_mul_ordinary_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    {x : ℝ} (hx : 0 ≤ x) :
    (19 / 20 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetFour x <
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let p := thetaCuspLikelihoodTailProbability B
  let e1 := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  let e4 := thetaCuspLikelihoodNormalizedMoment B 4
  let b1 := 2 * A * e1
  let b2 := 4 * (A ^ 2 * e2 - A * e1)
  let b3 := 8 * (A ^ 3 * e3 - 3 * A ^ 2 * e2 + A * e1)
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
    simpa only [e2, e3] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
  have he34 : 3 * e3 ≤ e4 := by
    simpa only [e3, e4] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 3
  have he3 : 0 < e3 := lt_of_lt_of_le (mul_pos (by norm_num) he2) he23
  have he4 : 0 < e4 := lt_of_lt_of_le (mul_pos (by norm_num) he3) he34
  have hpSmall : 400 * p < 1 := by
    simpa only [B, p] using
      four_hundred_mul_thetaCuspLikelihoodTailProbability_coordinate_lt_one hx
  have h22 : e2 ^ 2 ≤ p * e4 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 2 2
    simpa only [B, p, e2, e4, show 2 + 2 = 4 by norm_num, pow_two] using h
  have hp : 0 < p := by nlinarith [sq_pos_of_pos he2]
  have h11 : e1 ^ 2 ≤ p * e2 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 1 1
    simpa only [B, p, e1, e2, thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 1 = 2 by norm_num, pow_two] using h
  have h13 : e1 * e3 ≤ p * e4 := by
    simpa only [B, p, e1, e3, e4,
      thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 3 = 4 by norm_num] using
        thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 1 3
  have hb1 : 0 < b1 := by dsimp only [b1]; positivity
  have hAe2 : e1 < A * e2 := by
    have hmul := mul_lt_mul_of_pos_right hA he2
    nlinarith
  have hb2 : 0 < b2 := by
    have hmul := mul_lt_mul_of_pos_left hAe2 hA0
    dsimp only [b2]
    nlinarith
  have hb2Upper : b2 ≤ 4 * A ^ 2 * e2 := by
    dsimp only [b2]
    nlinarith [mul_pos hA0 he1]
  have hAe3 : 3 * e2 < A * e3 := by
    have hmul := mul_lt_mul_of_pos_right hA he3
    nlinarith
  have hb3 : 0 < b3 := by
    have hmul := mul_lt_mul_of_pos_left hAe3 (pow_pos hA0 2)
    dsimp only [b3]
    nlinarith [mul_pos hA0 he1]
  have he13nine : 9 * e1 ≤ e3 := by nlinarith
  have hA2 : 9 < A ^ 2 := by nlinarith [sq_pos_of_pos (sub_pos.mpr hA)]
  have hscaleA := mul_lt_mul_of_pos_right hA2 (mul_pos hA0 he1)
  have hfirst : 81 * A * e1 < 9 * A ^ 3 * e1 := by
    nlinarith
  have hsecond : 9 * A ^ 3 * e1 ≤ A ^ 3 * e3 := by
    have hmul := mul_le_mul_of_nonneg_left he13nine (pow_nonneg hA0.le 3)
    nlinarith
  have hAe1 : 81 * A * e1 ≤ A ^ 3 * e3 := le_trans hfirst.le hsecond
  have hb3Upper : b3 ≤ (656 / 81 : ℝ) * A ^ 3 * e3 := by
    dsimp only [b3]
    nlinarith [mul_nonneg (pow_nonneg hA0.le 2) he2.le]
  have hb4Lower : (32 / 5 : ℝ) * A ^ 4 * e4 ≤ b4 := by
    simpa only [A, B, e4, b4] using
      two_fifths_le_thetaCuspLikelihoodSourceOrdinaryJetFour hx
  have hb4 : 0 < b4 := lt_of_lt_of_le (by positivity) hb4Lower
  have hb1b3 : b1 * b3 ≤ (1312 / 81 : ℝ) * p * A ^ 4 * e4 := by
    calc
      b1 * b3 ≤ b1 * ((656 / 81 : ℝ) * A ^ 3 * e3) :=
        mul_le_mul_of_nonneg_left hb3Upper hb1.le
      _ = (1312 / 81 : ℝ) * A ^ 4 * (e1 * e3) := by dsimp only [b1]; ring
      _ ≤ (1312 / 81 : ℝ) * A ^ 4 * (p * e4) := by gcongr
      _ = (1312 / 81 : ℝ) * p * A ^ 4 * e4 := by ring
  have hb2sq : b2 ^ 2 ≤ 16 * p * A ^ 4 * e4 := by
    calc
      b2 ^ 2 ≤ (4 * A ^ 2 * e2) ^ 2 :=
        (sq_le_sq₀ hb2.le (by positivity)).2 hb2Upper
      _ = 16 * A ^ 4 * e2 ^ 2 := by ring
      _ ≤ 16 * A ^ 4 * (p * e4) := by gcongr
      _ = 16 * p * A ^ 4 * e4 := by ring
  have he1111 : e1 ^ 4 ≤ p ^ 3 * e4 := by
    calc
      e1 ^ 4 = (e1 ^ 2) * (e1 ^ 2) := by ring
      _ ≤ (p * e2) * (p * e2) := by gcongr
      _ = p ^ 2 * e2 ^ 2 := by ring
      _ ≤ p ^ 2 * (p * e4) := by gcongr
      _ = p ^ 3 * e4 := by ring
  have hb1four : b1 ^ 4 ≤ 16 * p ^ 3 * A ^ 4 * e4 := by
    calc
      b1 ^ 4 = 16 * A ^ 4 * e1 ^ 4 := by dsimp only [b1]; ring
      _ ≤ 16 * A ^ 4 * (p ^ 3 * e4) := by gcongr
      _ = 16 * p ^ 3 * A ^ 4 * e4 := by ring
  have hp3 : p ^ 3 < (1 / 400 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ (by nlinarith : p < (1 / 400 : ℝ)) hp.le (by norm_num)
  have hcoef : 4 * (1312 / 81 : ℝ) * p + 48 * p + 96 * p ^ 3 < (8 / 25 : ℝ) := by
    norm_num at hpSmall hp3 ⊢
    nlinarith
  have hweight : 0 < A ^ 4 * e4 := by positivity
  have hlossBudget :
      4 * ((1312 / 81 : ℝ) * p * A ^ 4 * e4) +
          3 * (16 * p * A ^ 4 * e4) +
          6 * (16 * p ^ 3 * A ^ 4 * e4) <
        (1 / 20 : ℝ) * b4 := by
    have hc := mul_lt_mul_of_pos_right hcoef hweight
    nlinarith
  have hdecomp :
      thetaCuspLikelihoodSourceLogPartitionJetFour x =
        b4 - 4 * b1 * b3 - 3 * b2 ^ 2 + 12 * b1 ^ 2 * b2 - 6 * b1 ^ 4 := by
    dsimp only [b1, b2, b3, b4, A, B, e1, e2, e3, e4]
    unfold thetaCuspLikelihoodSourceOrdinaryJetFour
      thetaCuspLikelihoodSourceLogPartitionJetFour thetaCuspLikelihoodFourthCumulant
      thetaCuspLikelihoodThirdCumulant
    rw [thetaCuspLikelihoodVariance_eq_normalizedMoment_two_sub_mean_sq]
    unfold thetaCuspLikelihoodNormalizedMoment thetaCuspLikelihoodMean
    ring
  rw [hdecomp]
  nlinarith [mul_nonneg (sq_nonneg b1) hb2.le]


end


end RHTower
