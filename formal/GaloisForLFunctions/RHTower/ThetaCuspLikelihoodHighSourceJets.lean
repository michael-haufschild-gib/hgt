import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodHighCumulantCalibration
import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenSixthJet

/-!
# Fifth and sixth source-coordinate theta likelihood jets

Extends exact likelihood cumulant ladder through sixth order.  New jets are literal derivatives
of logarithmic source partition, with fifth and sixth cumulants supplied by sharp modular
calibration.  No Xi divisor or zero-location input appears.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Fifth source-coordinate jet of the logarithmic higher-likelihood partition. -/
def thetaCuspLikelihoodSourceLogPartitionJetFive (x : ℝ) : ℝ :=
  -32 * thetaCuspSingleAtomReflectionScale 1 x ^ 5 *
      thetaCuspLikelihoodFifthCumulant (thetaCuspLikelihoodCoordinate x) +
    320 * thetaCuspSingleAtomReflectionScale 1 x ^ 4 *
      thetaCuspLikelihoodFourthCumulant (thetaCuspLikelihoodCoordinate x) -
    800 * thetaCuspSingleAtomReflectionScale 1 x ^ 3 *
      thetaCuspLikelihoodThirdCumulant (thetaCuspLikelihoodCoordinate x) +
    480 * thetaCuspSingleAtomReflectionScale 1 x ^ 2 *
      thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x) -
    32 * thetaCuspSingleAtomReflectionScale 1 x *
      thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)

/-- Sixth source-coordinate jet of the logarithmic higher-likelihood partition. -/
def thetaCuspLikelihoodSourceLogPartitionJetSix (x : ℝ) : ℝ :=
  64 * thetaCuspSingleAtomReflectionScale 1 x ^ 6 *
      thetaCuspLikelihoodSixthCumulant (thetaCuspLikelihoodCoordinate x) -
    960 * thetaCuspSingleAtomReflectionScale 1 x ^ 5 *
      thetaCuspLikelihoodFifthCumulant (thetaCuspLikelihoodCoordinate x) +
    4160 * thetaCuspSingleAtomReflectionScale 1 x ^ 4 *
      thetaCuspLikelihoodFourthCumulant (thetaCuspLikelihoodCoordinate x) -
    5760 * thetaCuspSingleAtomReflectionScale 1 x ^ 3 *
      thetaCuspLikelihoodThirdCumulant (thetaCuspLikelihoodCoordinate x) +
    1984 * thetaCuspSingleAtomReflectionScale 1 x ^ 2 *
      thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x) -
    64 * thetaCuspSingleAtomReflectionScale 1 x *
      thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)

/-- Sharp source-support margin for sixth ordinary score. At actual theta scale every positive
spectral atom lies beyond `A t > 47/5`, where one thirtieth of leading sixth monomial survives. -/
theorem one_thirtieth_mul_sourceLinearSixPolynomial_le
    {A t : ℝ} (hA : (47 / 15 : ℝ) < A) (ht : 3 ≤ t) :
    (1 / 30 : ℝ) * A ^ 6 * t ^ 6 ≤
      A ^ 6 * t ^ 6 - 15 * A ^ 5 * t ^ 5 + 65 * A ^ 4 * t ^ 4 -
        90 * A ^ 3 * t ^ 3 + 31 * A ^ 2 * t ^ 2 - A * t := by
  let z := A * t
  let y := z - 9
  have hz : (47 / 5 : ℝ) < z := by
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    have hmul := mul_lt_mul_of_pos_right hA ht0
    dsimp only [z]
    nlinarith
  have hy : (2 / 5 : ℝ) < y := by dsimp only [y]; linarith
  have hy0 : 0 ≤ y := by linarith
  have hy2 : (4 / 25 : ℝ) < y ^ 2 := by
    have hprod : 0 < (y - 2 / 5) * (y + 2 / 5) := by positivity
    nlinarith
  have hcore : 0 <
      (29951 / 2 : ℝ) * y ^ 2 + (93181 / 5 : ℝ) * y - 86517 / 10 := by
    nlinarith
  have hhigh : 0 ≤
      (29 / 30 : ℝ) * y ^ 6 + (186 / 5 : ℝ) * y ^ 5 +
        (1129 / 2 : ℝ) * y ^ 4 + 4194 * y ^ 3 := by positivity
  dsimp only [z, y] at hcore hhigh ⊢
  nlinarith [show
    A ^ 6 * t ^ 6 - 15 * A ^ 5 * t ^ 5 + 65 * A ^ 4 * t ^ 4 -
        90 * A ^ 3 * t ^ 3 + 31 * A ^ 2 * t ^ 2 - A * t -
          (1 / 30 : ℝ) * A ^ 6 * t ^ 6 =
      (29 / 30 : ℝ) * (A * t - 9) ^ 6 +
        (186 / 5 : ℝ) * (A * t - 9) ^ 5 +
        (1129 / 2 : ℝ) * (A * t - 9) ^ 4 +
        4194 * (A * t - 9) ^ 3 +
        (29951 / 2 : ℝ) * (A * t - 9) ^ 2 +
        (93181 / 5 : ℝ) * (A * t - 9) - 86517 / 10 by ring]

/-- Differentiating the fourth cumulant jet gives the literal fifth source jet. -/
theorem hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFour
    {x : ℝ} (hB : 0 < thetaCuspLikelihoodCoordinate x) :
    HasDerivAt thetaCuspLikelihoodSourceLogPartitionJetFour
      (thetaCuspLikelihoodSourceLogPartitionJetFive x) x := by
  have hscale := hasDerivAt_thetaCuspSingleAtomReflectionScale_one x
  have hcoord := hasDerivAt_thetaCuspLikelihoodCoordinate x
  have hm := (hasDerivAt_thetaCuspLikelihoodMean hB).comp x hcoord
  have hv := (hasDerivAt_thetaCuspLikelihoodVariance hB).comp x hcoord
  have hk3 := (hasDerivAt_thetaCuspLikelihoodThirdCumulant hB).comp x hcoord
  have hk4 := (hasDerivAt_thetaCuspLikelihoodFourthCumulant hB).comp x hcoord
  have hraw :=
    ((((hscale.pow 4).mul hk4).const_mul 16).sub
      (((hscale.pow 3).mul hk3).const_mul 96)).add
      (((hscale.pow 2).mul hv).const_mul 112) |>.sub
      ((hscale.mul hm).const_mul 16)
  unfold thetaCuspLikelihoodSourceLogPartitionJetFour
    thetaCuspLikelihoodSourceLogPartitionJetFive
  convert hraw using 1
  any_goals rfl
  · funext y
    simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply]
    ring
  · simp only [Function.comp_apply, Pi.pow_apply]
    ring

set_option maxHeartbeats 800000 in
/-- On source support `t ≥ 3` and scale `A > 3`, fifth score linear part retains at
least one sixth of leading fifth moment. -/
theorem one_sixth_mul_likelihoodSourceLinearFive_le
    {x : ℝ} (hx : 0 ≤ x) :
    (1 / 6 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 5 *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 5 ≤
      thetaCuspSingleAtomReflectionScale 1 x ^ 5 *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 5 -
        10 * thetaCuspSingleAtomReflectionScale 1 x ^ 4 *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 4 +
        25 * thetaCuspSingleAtomReflectionScale 1 x ^ 3 *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 3 -
        15 * thetaCuspSingleAtomReflectionScale 1 x ^ 2 *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 2 +
        thetaCuspSingleAtomReflectionScale 1 x *
          thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let μ := thetaCuspHigherLikelihoodTiltedMeasure B
  let f : ℝ → ℝ := fun t => (1 / 6 : ℝ) * A ^ 5 * t ^ 5
  let g : ℝ → ℝ := fun t =>
    A ^ 5 * t ^ 5 - 10 * A ^ 4 * t ^ 4 + 25 * A ^ 3 * t ^ 3 -
      15 * A ^ 2 * t ^ 2 + A * t
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hA : 3 < A := by
    simpa only [A] using
      three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx
  have h2 := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 2 hB
  have h3 := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 3 hB
  have h4 := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 4 hB
  have h5 := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 5 hB
  have h1 := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 1 hB
  have hf : Integrable f μ := by
    change Integrable (fun t : ℝ => ((1 / 6 : ℝ) * A ^ 5) * t ^ 5)
      (thetaCuspHigherLikelihoodTiltedMeasure B)
    exact h5.const_mul _
  have ha : Integrable (fun t : ℝ => A ^ 5 * t ^ 5) μ := by
    change Integrable (fun t : ℝ => A ^ 5 * t ^ 5)
      (thetaCuspHigherLikelihoodTiltedMeasure B)
    exact h5.const_mul _
  have hb : Integrable (fun t : ℝ => 10 * A ^ 4 * t ^ 4) μ := by
    change Integrable (fun t : ℝ => (10 * A ^ 4) * t ^ 4)
      (thetaCuspHigherLikelihoodTiltedMeasure B)
    exact h4.const_mul _
  have hc : Integrable (fun t : ℝ => 25 * A ^ 3 * t ^ 3) μ := by
    change Integrable (fun t : ℝ => (25 * A ^ 3) * t ^ 3)
      (thetaCuspHigherLikelihoodTiltedMeasure B)
    exact h3.const_mul _
  have hd : Integrable (fun t : ℝ => 15 * A ^ 2 * t ^ 2) μ := by
    change Integrable (fun t : ℝ => (15 * A ^ 2) * t ^ 2)
      (thetaCuspHigherLikelihoodTiltedMeasure B)
    exact h2.const_mul _
  have he : Integrable (fun t : ℝ => A * t) μ := by
    change Integrable (fun t : ℝ => A * t)
      (thetaCuspHigherLikelihoodTiltedMeasure B)
    simpa only [pow_one] using h1.const_mul A
  have hab := ha.sub hb
  have habc := hab.add hc
  have habcd := habc.sub hd
  have hg : Integrable g μ := by
    change Integrable
      ((((fun t : ℝ => A ^ 5 * t ^ 5) -
        (fun t : ℝ => 10 * A ^ 4 * t ^ 4)) +
        (fun t : ℝ => 25 * A ^ 3 * t ^ 3) -
        (fun t : ℝ => 15 * A ^ 2 * t ^ 2)) +
        (fun t : ℝ => A * t)) μ
    exact habcd.add he
  have hmono : (∫ t, f t ∂μ) ≤ ∫ t, g t ∂μ := by
    apply integral_mono_ae hf hg
    filter_upwards [ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure B] with t ht
    let z := A * t
    let y := z - 9
    have hz : 9 < z := by
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
      have hmul := mul_lt_mul_of_pos_right hA ht0
      dsimp only [z]
      nlinarith
    have hy : 0 ≤ y := by dsimp only [y]; linarith
    have hpoly : 0 ≤
        (5 / 6 : ℝ) * y ^ 4 + 20 * y ^ 3 + 160 * y ^ 2 +
          435 * y + 137 / 2 := by positivity
    have hprod : 0 ≤ z * ((5 / 6 : ℝ) * y ^ 4 + 20 * y ^ 3 +
        160 * y ^ 2 + 435 * y + 137 / 2) :=
      mul_nonneg (by linarith) hpoly
    dsimp only [f, g, z, y] at hprod ⊢
    nlinarith [show
      A ^ 5 * t ^ 5 - 10 * A ^ 4 * t ^ 4 + 25 * A ^ 3 * t ^ 3 -
          15 * A ^ 2 * t ^ 2 + A * t -
            (1 / 6 : ℝ) * A ^ 5 * t ^ 5 =
        (A * t) * ((5 / 6 : ℝ) * (A * t - 9) ^ 4 +
          20 * (A * t - 9) ^ 3 + 160 * (A * t - 9) ^ 2 +
          435 * (A * t - 9) + 137 / 2) by ring]
  have hleft :
      (∫ t, f t ∂μ) = (1 / 6 : ℝ) * A ^ 5 *
        thetaCuspHigherLikelihoodSpectralMoment B 5 := by
    unfold f thetaCuspHigherLikelihoodSpectralMoment
    rw [integral_const_mul]
  have hright :
      (∫ t, g t ∂μ) =
        A ^ 5 * thetaCuspHigherLikelihoodSpectralMoment B 5 -
          10 * A ^ 4 * thetaCuspHigherLikelihoodSpectralMoment B 4 +
          25 * A ^ 3 * thetaCuspHigherLikelihoodSpectralMoment B 3 -
          15 * A ^ 2 * thetaCuspHigherLikelihoodSpectralMoment B 2 +
          A * thetaCuspHigherLikelihoodSpectralMoment B 1 := by
    unfold g thetaCuspHigherLikelihoodSpectralMoment
    change
      integral μ
        (((((fun u : ℝ => A ^ 5 * u ^ 5) -
          (fun u : ℝ => 10 * A ^ 4 * u ^ 4)) +
          (fun u : ℝ => 25 * A ^ 3 * u ^ 3)) -
          (fun u : ℝ => 15 * A ^ 2 * u ^ 2)) +
          (fun u : ℝ => A * u)) = _
    rw [integral_add' habcd he, integral_sub' habc hd,
      integral_add' hab hc, integral_sub' ha hb]
    simp only [pow_one]
    simp only [integral_const_mul]
    rw [integral_const_mul A (fun a : ℝ => a)]
  rw [hleft, hright] at hmono
  have hraw := hmono
  change
    (1 / 6 : ℝ) * A ^ 5 *
          (thetaCuspHigherLikelihoodSpectralMoment B 5 / P) ≤
      A ^ 5 * (thetaCuspHigherLikelihoodSpectralMoment B 5 / P) -
        10 * A ^ 4 * (thetaCuspHigherLikelihoodSpectralMoment B 4 / P) +
        25 * A ^ 3 * (thetaCuspHigherLikelihoodSpectralMoment B 3 / P) -
        15 * A ^ 2 * (thetaCuspHigherLikelihoodSpectralMoment B 2 / P) +
        A * (thetaCuspHigherLikelihoodSpectralMoment B 1 / P)
  rw [show
      (1 / 6 : ℝ) * A ^ 5 *
          (thetaCuspHigherLikelihoodSpectralMoment B 5 / P) =
        ((1 / 6 : ℝ) * A ^ 5 *
          thetaCuspHigherLikelihoodSpectralMoment B 5) / P by ring,
    show
      A ^ 5 * (thetaCuspHigherLikelihoodSpectralMoment B 5 / P) -
          10 * A ^ 4 * (thetaCuspHigherLikelihoodSpectralMoment B 4 / P) +
          25 * A ^ 3 * (thetaCuspHigherLikelihoodSpectralMoment B 3 / P) -
          15 * A ^ 2 * (thetaCuspHigherLikelihoodSpectralMoment B 2 / P) +
          A * (thetaCuspHigherLikelihoodSpectralMoment B 1 / P) =
        (A ^ 5 * thetaCuspHigherLikelihoodSpectralMoment B 5 -
          10 * A ^ 4 * thetaCuspHigherLikelihoodSpectralMoment B 4 +
          25 * A ^ 3 * thetaCuspHigherLikelihoodSpectralMoment B 3 -
          15 * A ^ 2 * thetaCuspHigherLikelihoodSpectralMoment B 2 +
          A * thetaCuspHigherLikelihoodSpectralMoment B 1) / P by ring]
  exact (div_le_div_iff_of_pos_right hP).2 hraw

set_option maxHeartbeats 800000 in
theorem one_thirtieth_mul_likelihoodSourceLinearSix_le
    {x : ℝ} (hx : 0 ≤ x) :
    (1 / 30 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 6 *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 6 ≤
      thetaCuspSingleAtomReflectionScale 1 x ^ 6 *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 6 -
        15 * thetaCuspSingleAtomReflectionScale 1 x ^ 5 *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 5 +
        65 * thetaCuspSingleAtomReflectionScale 1 x ^ 4 *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 4 -
        90 * thetaCuspSingleAtomReflectionScale 1 x ^ 3 *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 3 +
        31 * thetaCuspSingleAtomReflectionScale 1 x ^ 2 *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 2 -
        thetaCuspSingleAtomReflectionScale 1 x *
          thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let μ := thetaCuspHigherLikelihoodTiltedMeasure B
  let f : ℝ → ℝ := fun t => (1 / 30 : ℝ) * A ^ 6 * t ^ 6
  let g : ℝ → ℝ := fun t =>
    A ^ 6 * t ^ 6 - 15 * A ^ 5 * t ^ 5 + 65 * A ^ 4 * t ^ 4 -
      90 * A ^ 3 * t ^ 3 + 31 * A ^ 2 * t ^ 2 - A * t
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hA : (47 / 15 : ℝ) < A := by
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    have hmul : Real.pi ≤ Real.pi * Real.exp (2 * x) :=
      le_mul_of_one_le_right Real.pi_pos.le he
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    nlinarith [Real.pi_gt_d2]
  have h1 := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 1 hB
  have h2 := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 2 hB
  have h3 := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 3 hB
  have h4 := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 4 hB
  have h5 := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 5 hB
  have h6 := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 6 hB
  have hf : Integrable f μ := by
    change Integrable (fun t : ℝ => ((1 / 30 : ℝ) * A ^ 6) * t ^ 6)
      (thetaCuspHigherLikelihoodTiltedMeasure B)
    exact h6.const_mul _
  have ha : Integrable (fun t : ℝ => A ^ 6 * t ^ 6) μ := h6.const_mul _
  have hb : Integrable (fun t : ℝ => 15 * A ^ 5 * t ^ 5) μ := by
    convert h5.const_mul (15 * A ^ 5) using 1
  have hc : Integrable (fun t : ℝ => 65 * A ^ 4 * t ^ 4) μ := by
    convert h4.const_mul (65 * A ^ 4) using 1
  have hd : Integrable (fun t : ℝ => 90 * A ^ 3 * t ^ 3) μ := by
    convert h3.const_mul (90 * A ^ 3) using 1
  have he : Integrable (fun t : ℝ => 31 * A ^ 2 * t ^ 2) μ := by
    convert h2.const_mul (31 * A ^ 2) using 1
  have hz : Integrable (fun t : ℝ => A * t) μ := by
    simpa only [pow_one] using h1.const_mul A
  have hg : Integrable g μ := by
    change Integrable (fun t : ℝ =>
      ((((A ^ 6 * t ^ 6 - 15 * A ^ 5 * t ^ 5) + 65 * A ^ 4 * t ^ 4) -
        90 * A ^ 3 * t ^ 3) + 31 * A ^ 2 * t ^ 2) - A * t) μ
    exact ((((ha.sub hb).add hc).sub hd).add he).sub hz
  have hmono : (∫ t, f t ∂μ) ≤ ∫ t, g t ∂μ := by
    apply integral_mono_ae hf hg
    filter_upwards [ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure B] with t ht
    exact one_thirtieth_mul_sourceLinearSixPolynomial_le hA ht
  have hleft :
      (∫ t, f t ∂μ) = (1 / 30 : ℝ) * A ^ 6 *
        thetaCuspHigherLikelihoodSpectralMoment B 6 := by
    unfold f thetaCuspHigherLikelihoodSpectralMoment
    rw [integral_const_mul]
  have hright :
      (∫ t, g t ∂μ) =
        A ^ 6 * thetaCuspHigherLikelihoodSpectralMoment B 6 -
          15 * A ^ 5 * thetaCuspHigherLikelihoodSpectralMoment B 5 +
          65 * A ^ 4 * thetaCuspHigherLikelihoodSpectralMoment B 4 -
          90 * A ^ 3 * thetaCuspHigherLikelihoodSpectralMoment B 3 +
          31 * A ^ 2 * thetaCuspHigherLikelihoodSpectralMoment B 2 -
          A * thetaCuspHigherLikelihoodSpectralMoment B 1 := by
    unfold g thetaCuspHigherLikelihoodSpectralMoment
    rw [show (fun t : ℝ =>
        ((((A ^ 6 * t ^ 6 - 15 * A ^ 5 * t ^ 5) + 65 * A ^ 4 * t ^ 4) -
          90 * A ^ 3 * t ^ 3) + 31 * A ^ 2 * t ^ 2) - A * t) =
        (((((fun t : ℝ => A ^ 6 * t ^ 6) -
          (fun t : ℝ => 15 * A ^ 5 * t ^ 5)) +
          (fun t : ℝ => 65 * A ^ 4 * t ^ 4)) -
          (fun t : ℝ => 90 * A ^ 3 * t ^ 3)) +
          (fun t : ℝ => 31 * A ^ 2 * t ^ 2)) -
          (fun t : ℝ => A * t) by
      funext t
      simp only [Pi.add_apply, Pi.sub_apply]]
    rw [integral_sub' ((((ha.sub hb).add hc).sub hd).add he) hz,
      integral_add' (((ha.sub hb).add hc).sub hd) he,
      integral_sub' ((ha.sub hb).add hc) hd,
      integral_add' (ha.sub hb) hc,
      integral_sub' ha hb]
    simp only [integral_const_mul]
    rw [integral_const_mul A (fun t : ℝ => t)]
    simp only [μ, pow_one]
  rw [hleft, hright] at hmono
  have hraw := hmono
  change
    (1 / 30 : ℝ) * A ^ 6 *
          (thetaCuspHigherLikelihoodSpectralMoment B 6 / P) ≤
      A ^ 6 * (thetaCuspHigherLikelihoodSpectralMoment B 6 / P) -
        15 * A ^ 5 * (thetaCuspHigherLikelihoodSpectralMoment B 5 / P) +
        65 * A ^ 4 * (thetaCuspHigherLikelihoodSpectralMoment B 4 / P) -
        90 * A ^ 3 * (thetaCuspHigherLikelihoodSpectralMoment B 3 / P) +
        31 * A ^ 2 * (thetaCuspHigherLikelihoodSpectralMoment B 2 / P) -
        A * (thetaCuspHigherLikelihoodSpectralMoment B 1 / P)
  rw [show
      (1 / 30 : ℝ) * A ^ 6 *
          (thetaCuspHigherLikelihoodSpectralMoment B 6 / P) =
        ((1 / 30 : ℝ) * A ^ 6 *
          thetaCuspHigherLikelihoodSpectralMoment B 6) / P by ring,
    show
      A ^ 6 * (thetaCuspHigherLikelihoodSpectralMoment B 6 / P) -
          15 * A ^ 5 * (thetaCuspHigherLikelihoodSpectralMoment B 5 / P) +
          65 * A ^ 4 * (thetaCuspHigherLikelihoodSpectralMoment B 4 / P) -
          90 * A ^ 3 * (thetaCuspHigherLikelihoodSpectralMoment B 3 / P) +
          31 * A ^ 2 * (thetaCuspHigherLikelihoodSpectralMoment B 2 / P) -
          A * (thetaCuspHigherLikelihoodSpectralMoment B 1 / P) =
        (A ^ 6 * thetaCuspHigherLikelihoodSpectralMoment B 6 -
          15 * A ^ 5 * thetaCuspHigherLikelihoodSpectralMoment B 5 +
          65 * A ^ 4 * thetaCuspHigherLikelihoodSpectralMoment B 4 -
          90 * A ^ 3 * thetaCuspHigherLikelihoodSpectralMoment B 3 +
          31 * A ^ 2 * thetaCuspHigherLikelihoodSpectralMoment B 2 -
          A * thetaCuspHigherLikelihoodSpectralMoment B 1) / P by ring]
  exact (div_le_div_iff_of_pos_right hP).2 hraw


/-- Differentiating the fifth cumulant jet gives the literal sixth source jet. -/
theorem hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFive
    {x : ℝ} (hB : 0 < thetaCuspLikelihoodCoordinate x) :
    HasDerivAt thetaCuspLikelihoodSourceLogPartitionJetFive
      (thetaCuspLikelihoodSourceLogPartitionJetSix x) x := by
  have hscale := hasDerivAt_thetaCuspSingleAtomReflectionScale_one x
  have hcoord := hasDerivAt_thetaCuspLikelihoodCoordinate x
  have hm := (hasDerivAt_thetaCuspLikelihoodMean hB).comp x hcoord
  have hv := (hasDerivAt_thetaCuspLikelihoodVariance hB).comp x hcoord
  have hk3 := (hasDerivAt_thetaCuspLikelihoodThirdCumulant hB).comp x hcoord
  have hk4 := (hasDerivAt_thetaCuspLikelihoodFourthCumulant hB).comp x hcoord
  have hk5 := (hasDerivAt_thetaCuspLikelihoodFifthCumulant hB).comp x hcoord
  have hraw :=
    (((((hscale.pow 5).mul hk5).const_mul (-32)).add
      (((hscale.pow 4).mul hk4).const_mul 320)).sub
      (((hscale.pow 3).mul hk3).const_mul 800)).add
      (((hscale.pow 2).mul hv).const_mul 480) |>.sub
      ((hscale.mul hm).const_mul 32)
  unfold thetaCuspLikelihoodSourceLogPartitionJetFive
    thetaCuspLikelihoodSourceLogPartitionJetSix
  convert hraw using 1
  any_goals rfl
  · funext y
    simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply]
    ring
  · simp only [Function.comp_apply, Pi.pow_apply]
    ring

set_option maxHeartbeats 800000 in
/-- Unconditional fifth source-jet orientation throughout nonnegative source half-line. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetFive_neg
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodSourceLogPartitionJetFive x < 0 := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let p := thetaCuspLikelihoodTailProbability B
  let m := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  let e4 := thetaCuspLikelihoodNormalizedMoment B 4
  let e5 := thetaCuspLikelihoodNormalizedMoment B 5
  have hB : 0 < B := by
    simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hA : 3 < A := by
    simpa only [A] using
      three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx
  have hA0 : 0 < A := by linarith
  have hm : 0 < m := by
    simpa only [m] using thetaCuspLikelihoodMean_pos hB
  have hmSmall : 60 * m < 1 := by
    simpa only [B, m] using
      sixty_mul_thetaCuspLikelihoodMean_coordinate_lt_one hx
  have hpSmall : 180 * p < 1 := by
    simpa only [B, p] using
      one_hundred_eighty_mul_thetaCuspLikelihoodTailProbability_coordinate_lt_one hx
  have he2 : 0 < e2 := by
    simpa only [e2] using thetaCuspLikelihoodNormalizedMoment_two_pos hB
  have he23 : 3 * e2 ≤ e3 := by
    simpa only [e2, e3] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
  have he34 : 3 * e3 ≤ e4 := by
    simpa only [e3, e4] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 3
  have he45 : 3 * e4 ≤ e5 := by
    simpa only [e4, e5] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 4
  have he3 : 0 < e3 :=
    lt_of_lt_of_le (mul_pos (by norm_num) he2) he23
  have he4 : 0 < e4 :=
    lt_of_lt_of_le (mul_pos (by norm_num) he3) he34
  have he5 : 0 < e5 :=
    lt_of_lt_of_le (mul_pos (by norm_num) he4) he45
  have he25 : 27 * e2 ≤ e5 := by nlinarith
  have hmomentProduct : e2 * e3 ≤ p * e5 := by
    simpa only [B, p, e2, e3, e5, show 2 + 3 = 5 by norm_num] using
      thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 2 3
  have hfirst : 5 * m * e4 < e5 / 36 := by
    have hprod : 0 < (1 - 60 * m) * e4 := by positivity
    nlinarith
  have hsecond : 10 * e2 * e3 < e5 / 18 := by
    have hprod : 0 < (1 - 180 * p) * e5 := by positivity
    nlinarith
  have hmOne : m < 1 := by nlinarith
  have hmSqOne : m ^ 2 < 1 := pow_lt_one₀ hm.le hmOne (by norm_num)
  have hmCube : m ^ 3 < m := by
    calc
      m ^ 3 = m * m ^ 2 := by ring
      _ < m * 1 := mul_lt_mul_of_pos_left hmSqOne hm
      _ = m := by ring
  have hthird : 60 * m ^ 3 * e2 < e5 / 27 := by
    have hcoef : 60 * m ^ 3 < 1 := by nlinarith
    have hmul := mul_lt_mul_of_pos_right hcoef he2
    nlinarith
  have hfirstA : 5 * A ^ 5 * m * e4 < A ^ 5 * e5 / 36 := by
    have hmul := mul_lt_mul_of_pos_left hfirst (pow_pos hA0 5)
    nlinarith
  have hsecondA : 10 * A ^ 5 * e2 * e3 < A ^ 5 * e5 / 18 := by
    have hmul := mul_lt_mul_of_pos_left hsecond (pow_pos hA0 5)
    nlinarith
  have hthirdA : 60 * A ^ 5 * m ^ 3 * e2 < A ^ 5 * e5 / 27 := by
    have hmul := mul_lt_mul_of_pos_left hthird (pow_pos hA0 5)
    nlinarith
  have hmSqSmall : 3600 * m ^ 2 < 1 := by
    have hprod : 0 < (1 - 60 * m) * (1 + 60 * m) := by positivity
    nlinarith
  have hcoefFour : 240000 * m ^ 2 < 200 / 3 := by nlinarith
  have hAe5 : 81 * e2 < A * e5 := by
    have hmul := mul_lt_mul_of_pos_right hA he5
    nlinarith
  have hrawFour : 240000 * m ^ 2 * e2 < A * e5 := by
    have hmul := mul_lt_mul_of_pos_right hcoefFour he2
    nlinarith
  have hfourthA :
      120 * A ^ 4 * m ^ 2 * e2 < A ^ 5 * e5 / 2000 := by
    have hmul := mul_lt_mul_of_pos_left hrawFour (pow_pos hA0 4)
    calc
      120 * A ^ 4 * m ^ 2 * e2 =
          (A ^ 4 * (240000 * m ^ 2 * e2)) / 2000 := by ring
      _ < (A ^ 4 * (A * e5)) / 2000 :=
        div_lt_div_of_pos_right hmul (by norm_num)
      _ = A ^ 5 * e5 / 2000 := by ring
  have hcoefFive : 13500 * m < 225 := by nlinarith
  have hA_sq : 9 < A ^ 2 := by nlinarith [sq_nonneg (A - 3)]
  have hA2e5 : 243 * e2 < A ^ 2 * e5 := by
    have hmul := mul_lt_mul_of_pos_right hA_sq he5
    nlinarith
  have hrawFive : 13500 * m * e2 < A ^ 2 * e5 := by
    have hmul := mul_lt_mul_of_pos_right hcoefFive he2
    nlinarith
  have hfifthA :
      75 * A ^ 3 * m * e2 < A ^ 5 * e5 / 180 := by
    have hmul := mul_lt_mul_of_pos_left hrawFive (pow_pos hA0 3)
    calc
      75 * A ^ 3 * m * e2 =
          (A ^ 3 * (13500 * m * e2)) / 180 := by ring
      _ < (A ^ 3 * (A ^ 2 * e5)) / 180 :=
        div_lt_div_of_pos_right hmul (by norm_num)
      _ = A ^ 5 * e5 / 180 := by ring
  have hnegative :
      5 * A ^ 5 * m * e4 + 10 * A ^ 5 * e2 * e3 +
          60 * A ^ 5 * m ^ 3 * e2 + 120 * A ^ 4 * m ^ 2 * e2 +
          75 * A ^ 3 * m * e2 < A ^ 5 * e5 / 6 := by
    have hAe : 0 < A ^ 5 * e5 := mul_pos (pow_pos hA0 5) he5
    nlinarith
  have hlinear :
      (1 / 6 : ℝ) * A ^ 5 * e5 ≤
        A ^ 5 * e5 - 10 * A ^ 4 * e4 + 25 * A ^ 3 * e3 -
          15 * A ^ 2 * e2 + A * m := by
    simpa only [A, B, m, e2, e3, e4, e5] using
      one_sixth_mul_likelihoodSourceLinearFive_le hx
  have hpos1 : 0 ≤ 20 * A ^ 5 * m ^ 2 * e3 := by positivity
  have hpos2 : 0 ≤ 30 * A ^ 5 * m * e2 ^ 2 := by positivity
  have hpos3 : 0 ≤ 24 * A ^ 5 * m ^ 5 := by positivity
  have hpos4 : 0 ≤ 40 * A ^ 4 * m * e3 := by positivity
  have hpos5 : 0 ≤ 30 * A ^ 4 * e2 ^ 2 := by positivity
  have hpos6 : 0 ≤ 60 * A ^ 4 * m ^ 4 := by positivity
  have hpos7 : 0 ≤ 50 * A ^ 3 * m ^ 3 := by positivity
  have hpos8 : 0 ≤ 15 * A ^ 2 * m ^ 2 := by positivity
  dsimp only [A, B, p, m, e2, e3, e4, e5] at *
  unfold thetaCuspLikelihoodSourceLogPartitionJetFive
    thetaCuspLikelihoodFifthCumulant thetaCuspLikelihoodFourthCumulant
    thetaCuspLikelihoodThirdCumulant
  rw [thetaCuspLikelihoodVariance_eq_normalizedMoment_two_sub_mean_sq]
  unfold thetaCuspLikelihoodNormalizedMoment at *
  nlinarith

end

end RHTower
