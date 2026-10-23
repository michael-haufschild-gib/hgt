import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodHighCumulantCalibration
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
  -32 * thetaCuspSingleAtomReflectionScale 1 x ^ (5 : ℕ) *
      thetaCuspLikelihoodFifthCumulant (thetaCuspLikelihoodCoordinate x) +
    320 * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) *
      thetaCuspLikelihoodFourthCumulant (thetaCuspLikelihoodCoordinate x) -
    800 * thetaCuspSingleAtomReflectionScale 1 x ^ (3 : ℕ) *
      thetaCuspLikelihoodThirdCumulant (thetaCuspLikelihoodCoordinate x) +
    480 * thetaCuspSingleAtomReflectionScale 1 x ^ (2 : ℕ) *
      thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x) -
    32 * thetaCuspSingleAtomReflectionScale 1 x *
      thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)

/-- Sixth source-coordinate jet of the logarithmic higher-likelihood partition. -/
def thetaCuspLikelihoodSourceLogPartitionJetSix (x : ℝ) : ℝ :=
  64 * thetaCuspSingleAtomReflectionScale 1 x ^ (6 : ℕ) *
      thetaCuspLikelihoodSixthCumulant (thetaCuspLikelihoodCoordinate x) -
    960 * thetaCuspSingleAtomReflectionScale 1 x ^ (5 : ℕ) *
      thetaCuspLikelihoodFifthCumulant (thetaCuspLikelihoodCoordinate x) +
    4160 * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) *
      thetaCuspLikelihoodFourthCumulant (thetaCuspLikelihoodCoordinate x) -
    5760 * thetaCuspSingleAtomReflectionScale 1 x ^ (3 : ℕ) *
      thetaCuspLikelihoodThirdCumulant (thetaCuspLikelihoodCoordinate x) +
    1984 * thetaCuspSingleAtomReflectionScale 1 x ^ (2 : ℕ) *
      thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x) -
    64 * thetaCuspSingleAtomReflectionScale 1 x *
      thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)

/-- Sharp source-support margin for sixth ordinary score. At actual theta scale every positive
spectral atom lies beyond `A t > 47/5`, where one thirtieth of leading sixth monomial survives. -/
theorem one_thirtieth_mul_sourceLinearSixPolynomial_le
    {A t : ℝ} (hA : (47 / 15 : ℝ) < A) (ht : 3 ≤ t) :
    (1 / 30 : ℝ) * A ^ (6 : ℕ) * t ^ (6 : ℕ) ≤
      A ^ (6 : ℕ) * t ^ (6 : ℕ) - 15 * A ^ (5 : ℕ) * t ^ (5 : ℕ) + 65 * A ^ (4 : ℕ) * t ^ (4 : ℕ) -
        90 * A ^ (3 : ℕ) * t ^ (3 : ℕ) + 31 * A ^ (2 : ℕ) * t ^ (2 : ℕ) - A * t := by
  let z := A * t
  let y := z - 9
  have hz : (47 / 5 : ℝ) < z := by
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    have hmul := mul_lt_mul_of_pos_right hA ht0
    dsimp only [z]
    nlinarith
  have hy : (2 / 5 : ℝ) < y := by dsimp only [y]; linarith
  have hy0 : 0 ≤ y := by linarith
  have hy2 : (4 / 25 : ℝ) < y ^ (2 : ℕ) := by
    have hprod : 0 < (y - 2 / 5) * (y + 2 / 5) := by positivity
    nlinarith
  have hcore : 0 <
      (29951 / 2 : ℝ) * y ^ (2 : ℕ) + (93181 / 5 : ℝ) * y - 86517 / 10 := by
    nlinarith
  have hhigh : 0 ≤
      (29 / 30 : ℝ) * y ^ (6 : ℕ) + (186 / 5 : ℝ) * y ^ (5 : ℕ) +
        (1129 / 2 : ℝ) * y ^ (4 : ℕ) + 4194 * y ^ (3 : ℕ) := by positivity
  dsimp only [z, y] at hcore hhigh ⊢
  nlinarith [show
    A ^ (6 : ℕ) * t ^ (6 : ℕ) - 15 * A ^ (5 : ℕ) * t ^ (5 : ℕ) + 65 * A ^ (4 : ℕ) * t ^ (4 : ℕ) -
        90 * A ^ (3 : ℕ) * t ^ (3 : ℕ) + 31 * A ^ (2 : ℕ) * t ^ (2 : ℕ) - A * t -
          (1 / 30 : ℝ) * A ^ (6 : ℕ) * t ^ (6 : ℕ) =
      (29 / 30 : ℝ) * (A * t - 9) ^ (6 : ℕ) +
        (186 / 5 : ℝ) * (A * t - 9) ^ (5 : ℕ) +
        (1129 / 2 : ℝ) * (A * t - 9) ^ (4 : ℕ) +
        4194 * (A * t - 9) ^ (3 : ℕ) +
        (29951 / 2 : ℝ) * (A * t - 9) ^ (2 : ℕ) +
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

/-- On source support `t ≥ 3` and scale `A > 3`, fifth score linear part retains at
least one sixth of leading fifth moment. -/
theorem one_sixth_mul_likelihoodSourceLinearFive_le
    {x : ℝ} (hx : 0 ≤ x) :
    (1 / 6 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ (5 : ℕ) *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 5 ≤
      thetaCuspSingleAtomReflectionScale 1 x ^ (5 : ℕ) *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 5 -
        10 * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 4 +
        25 * thetaCuspSingleAtomReflectionScale 1 x ^ (3 : ℕ) *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 3 -
        15 * thetaCuspSingleAtomReflectionScale 1 x ^ (2 : ℕ) *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 2 +
        thetaCuspSingleAtomReflectionScale 1 x *
          thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let μ := thetaCuspHigherLikelihoodTiltedMeasure B
  let f : ℝ → ℝ := fun t => (1 / 6 : ℝ) * A ^ (5 : ℕ) * t ^ (5 : ℕ)
  let g : ℝ → ℝ := fun t =>
    A ^ (5 : ℕ) * t ^ (5 : ℕ) - 10 * A ^ (4 : ℕ) * t ^ (4 : ℕ) + 25 * A ^ (3 : ℕ) * t ^ (3 : ℕ) -
      15 * A ^ (2 : ℕ) * t ^ (2 : ℕ) + A * t
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
    change Integrable (fun t : ℝ => ((1 / 6 : ℝ) * A ^ (5 : ℕ)) * t ^ (5 : ℕ))
      (thetaCuspHigherLikelihoodTiltedMeasure B)
    exact h5.const_mul _
  have ha : Integrable (fun t : ℝ => A ^ (5 : ℕ) * t ^ (5 : ℕ)) μ := by
    change Integrable (fun t : ℝ => A ^ (5 : ℕ) * t ^ (5 : ℕ))
      (thetaCuspHigherLikelihoodTiltedMeasure B)
    exact h5.const_mul _
  have hb : Integrable (fun t : ℝ => 10 * A ^ (4 : ℕ) * t ^ (4 : ℕ)) μ := by
    change Integrable (fun t : ℝ => (10 * A ^ (4 : ℕ)) * t ^ (4 : ℕ))
      (thetaCuspHigherLikelihoodTiltedMeasure B)
    exact h4.const_mul _
  have hc : Integrable (fun t : ℝ => 25 * A ^ (3 : ℕ) * t ^ (3 : ℕ)) μ := by
    change Integrable (fun t : ℝ => (25 * A ^ (3 : ℕ)) * t ^ (3 : ℕ))
      (thetaCuspHigherLikelihoodTiltedMeasure B)
    exact h3.const_mul _
  have hd : Integrable (fun t : ℝ => 15 * A ^ (2 : ℕ) * t ^ (2 : ℕ)) μ := by
    change Integrable (fun t : ℝ => (15 * A ^ (2 : ℕ)) * t ^ (2 : ℕ))
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
      ((((fun t : ℝ => A ^ (5 : ℕ) * t ^ (5 : ℕ)) -
        (fun t : ℝ => 10 * A ^ (4 : ℕ) * t ^ (4 : ℕ))) +
        (fun t : ℝ => 25 * A ^ (3 : ℕ) * t ^ (3 : ℕ)) -
        (fun t : ℝ => 15 * A ^ (2 : ℕ) * t ^ (2 : ℕ))) +
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
      linarith only [hmul, ht]
    have hy : 0 ≤ y := by dsimp only [y]; linarith only [hz]
    have hpoly : 0 ≤
        (5 / 6 : ℝ) * y ^ (4 : ℕ) + 20 * y ^ (3 : ℕ) + 160 * y ^ (2 : ℕ) +
          435 * y + 137 / 2 := by positivity
    have hprod : 0 ≤ z * ((5 / 6 : ℝ) * y ^ (4 : ℕ) + 20 * y ^ (3 : ℕ) +
        160 * y ^ (2 : ℕ) + 435 * y + 137 / 2) :=
      mul_nonneg (by linarith only [hz]) hpoly
    dsimp only [f, g, z, y] at hprod ⊢
    linarith only [hprod, show
      A ^ (5 : ℕ) * t ^ (5 : ℕ) - 10 * A ^ (4 : ℕ) * t ^ (4 : ℕ) + 25 * A ^ (3 : ℕ) * t ^ (3 : ℕ) -
          15 * A ^ (2 : ℕ) * t ^ (2 : ℕ) + A * t -
            (1 / 6 : ℝ) * A ^ (5 : ℕ) * t ^ (5 : ℕ) =
        (A * t) * ((5 / 6 : ℝ) * (A * t - 9) ^ (4 : ℕ) +
          20 * (A * t - 9) ^ (3 : ℕ) + 160 * (A * t - 9) ^ (2 : ℕ) +
          435 * (A * t - 9) + 137 / 2) by ring]
  have hleft :
      (∫ t, f t ∂μ) = (1 / 6 : ℝ) * A ^ (5 : ℕ) *
        thetaCuspHigherLikelihoodSpectralMoment B 5 := by
    unfold f thetaCuspHigherLikelihoodSpectralMoment
    rw [integral_const_mul]
  have hright :
      (∫ t, g t ∂μ) =
        A ^ (5 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 5 -
          10 * A ^ (4 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 4 +
          25 * A ^ (3 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 3 -
          15 * A ^ (2 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 2 +
          A * thetaCuspHigherLikelihoodSpectralMoment B 1 := by
    unfold g thetaCuspHigherLikelihoodSpectralMoment
    change
      integral μ
        (((((fun u : ℝ => A ^ (5 : ℕ) * u ^ (5 : ℕ)) -
          (fun u : ℝ => 10 * A ^ (4 : ℕ) * u ^ (4 : ℕ))) +
          (fun u : ℝ => 25 * A ^ (3 : ℕ) * u ^ (3 : ℕ))) -
          (fun u : ℝ => 15 * A ^ (2 : ℕ) * u ^ (2 : ℕ))) +
          (fun u : ℝ => A * u)) = _
    rw [integral_add' habcd he, integral_sub' habc hd,
      integral_add' hab hc, integral_sub' ha hb]
    simp only [pow_one]
    simp only [integral_const_mul]
    rw [integral_const_mul A (fun a : ℝ => a)]
  rw [hleft, hright] at hmono
  have hraw := hmono
  change
    (1 / 6 : ℝ) * A ^ (5 : ℕ) *
          (thetaCuspHigherLikelihoodSpectralMoment B 5 / P) ≤
      A ^ (5 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 5 / P) -
        10 * A ^ (4 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 4 / P) +
        25 * A ^ (3 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 3 / P) -
        15 * A ^ (2 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 2 / P) +
        A * (thetaCuspHigherLikelihoodSpectralMoment B 1 / P)
  rw [show
      (1 / 6 : ℝ) * A ^ (5 : ℕ) *
          (thetaCuspHigherLikelihoodSpectralMoment B 5 / P) =
        ((1 / 6 : ℝ) * A ^ (5 : ℕ) *
          thetaCuspHigherLikelihoodSpectralMoment B 5) / P by ring,
    show
      A ^ (5 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 5 / P) -
          10 * A ^ (4 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 4 / P) +
          25 * A ^ (3 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 3 / P) -
          15 * A ^ (2 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 2 / P) +
          A * (thetaCuspHigherLikelihoodSpectralMoment B 1 / P) =
        (A ^ (5 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 5 -
          10 * A ^ (4 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 4 +
          25 * A ^ (3 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 3 -
          15 * A ^ (2 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 2 +
          A * thetaCuspHigherLikelihoodSpectralMoment B 1) / P by ring]
  exact (div_le_div_iff_of_pos_right hP).2 hraw

theorem one_thirtieth_mul_likelihoodSourceLinearSix_le
    {x : ℝ} (hx : 0 ≤ x) :
    (1 / 30 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ (6 : ℕ) *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 6 ≤
      thetaCuspSingleAtomReflectionScale 1 x ^ (6 : ℕ) *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 6 -
        15 * thetaCuspSingleAtomReflectionScale 1 x ^ (5 : ℕ) *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 5 +
        65 * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 4 -
        90 * thetaCuspSingleAtomReflectionScale 1 x ^ (3 : ℕ) *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 3 +
        31 * thetaCuspSingleAtomReflectionScale 1 x ^ (2 : ℕ) *
          thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 2 -
        thetaCuspSingleAtomReflectionScale 1 x *
          thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let μ := thetaCuspHigherLikelihoodTiltedMeasure B
  let f : ℝ → ℝ := fun t => (1 / 30 : ℝ) * A ^ (6 : ℕ) * t ^ (6 : ℕ)
  let g : ℝ → ℝ := fun t =>
    A ^ (6 : ℕ) * t ^ (6 : ℕ) - 15 * A ^ (5 : ℕ) * t ^ (5 : ℕ) + 65 * A ^ (4 : ℕ) * t ^ (4 : ℕ) -
      90 * A ^ (3 : ℕ) * t ^ (3 : ℕ) + 31 * A ^ (2 : ℕ) * t ^ (2 : ℕ) - A * t
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hA : (47 / 15 : ℝ) < A := by
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    have hmul : Real.pi ≤ Real.pi * Real.exp (2 * x) :=
      le_mul_of_one_le_right Real.pi_pos.le he
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    linarith only [hmul, Real.pi_gt_d2]
  have h1 := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 1 hB
  have h2 := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 2 hB
  have h3 := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 3 hB
  have h4 := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 4 hB
  have h5 := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 5 hB
  have h6 := integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 6 hB
  have hf : Integrable f μ := by
    change Integrable (fun t : ℝ => ((1 / 30 : ℝ) * A ^ (6 : ℕ)) * t ^ (6 : ℕ))
      (thetaCuspHigherLikelihoodTiltedMeasure B)
    exact h6.const_mul _
  have ha : Integrable (fun t : ℝ => A ^ (6 : ℕ) * t ^ (6 : ℕ)) μ := h6.const_mul _
  have hb : Integrable (fun t : ℝ => 15 * A ^ (5 : ℕ) * t ^ (5 : ℕ)) μ := by
    convert h5.const_mul (15 * A ^ (5 : ℕ)) using 1
  have hc : Integrable (fun t : ℝ => 65 * A ^ (4 : ℕ) * t ^ (4 : ℕ)) μ := by
    convert h4.const_mul (65 * A ^ (4 : ℕ)) using 1
  have hd : Integrable (fun t : ℝ => 90 * A ^ (3 : ℕ) * t ^ (3 : ℕ)) μ := by
    convert h3.const_mul (90 * A ^ (3 : ℕ)) using 1
  have he : Integrable (fun t : ℝ => 31 * A ^ (2 : ℕ) * t ^ (2 : ℕ)) μ := by
    convert h2.const_mul (31 * A ^ (2 : ℕ)) using 1
  have hz : Integrable (fun t : ℝ => A * t) μ := by
    simpa only [pow_one] using h1.const_mul A
  have hg : Integrable g μ := by
    change Integrable (fun t : ℝ =>
      ((((A ^ (6 : ℕ) * t ^ (6 : ℕ) - 15 * A ^ (5 : ℕ) * t ^ (5 : ℕ)) + 65 * A ^ (4 : ℕ) * t ^ (4 : ℕ)) -
        90 * A ^ (3 : ℕ) * t ^ (3 : ℕ)) + 31 * A ^ (2 : ℕ) * t ^ (2 : ℕ)) - A * t) μ
    exact ((((ha.sub hb).add hc).sub hd).add he).sub hz
  have hmono : (∫ t, f t ∂μ) ≤ ∫ t, g t ∂μ := by
    apply integral_mono_ae hf hg
    filter_upwards [ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure B] with t ht
    exact one_thirtieth_mul_sourceLinearSixPolynomial_le hA ht
  have hleft :
      (∫ t, f t ∂μ) = (1 / 30 : ℝ) * A ^ (6 : ℕ) *
        thetaCuspHigherLikelihoodSpectralMoment B 6 := by
    unfold f thetaCuspHigherLikelihoodSpectralMoment
    rw [integral_const_mul]
  have hright :
      (∫ t, g t ∂μ) =
        A ^ (6 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 6 -
          15 * A ^ (5 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 5 +
          65 * A ^ (4 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 4 -
          90 * A ^ (3 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 3 +
          31 * A ^ (2 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 2 -
          A * thetaCuspHigherLikelihoodSpectralMoment B 1 := by
    unfold g thetaCuspHigherLikelihoodSpectralMoment
    rw [show (fun t : ℝ =>
        ((((A ^ (6 : ℕ) * t ^ (6 : ℕ) - 15 * A ^ (5 : ℕ) * t ^ (5 : ℕ)) + 65 * A ^ (4 : ℕ) * t ^ (4 : ℕ)) -
          90 * A ^ (3 : ℕ) * t ^ (3 : ℕ)) + 31 * A ^ (2 : ℕ) * t ^ (2 : ℕ)) - A * t) =
        (((((fun t : ℝ => A ^ (6 : ℕ) * t ^ (6 : ℕ)) -
          (fun t : ℝ => 15 * A ^ (5 : ℕ) * t ^ (5 : ℕ))) +
          (fun t : ℝ => 65 * A ^ (4 : ℕ) * t ^ (4 : ℕ))) -
          (fun t : ℝ => 90 * A ^ (3 : ℕ) * t ^ (3 : ℕ))) +
          (fun t : ℝ => 31 * A ^ (2 : ℕ) * t ^ (2 : ℕ))) -
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
    (1 / 30 : ℝ) * A ^ (6 : ℕ) *
          (thetaCuspHigherLikelihoodSpectralMoment B 6 / P) ≤
      A ^ (6 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 6 / P) -
        15 * A ^ (5 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 5 / P) +
        65 * A ^ (4 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 4 / P) -
        90 * A ^ (3 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 3 / P) +
        31 * A ^ (2 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 2 / P) -
        A * (thetaCuspHigherLikelihoodSpectralMoment B 1 / P)
  rw [show
      (1 / 30 : ℝ) * A ^ (6 : ℕ) *
          (thetaCuspHigherLikelihoodSpectralMoment B 6 / P) =
        ((1 / 30 : ℝ) * A ^ (6 : ℕ) *
          thetaCuspHigherLikelihoodSpectralMoment B 6) / P by ring,
    show
      A ^ (6 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 6 / P) -
          15 * A ^ (5 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 5 / P) +
          65 * A ^ (4 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 4 / P) -
          90 * A ^ (3 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 3 / P) +
          31 * A ^ (2 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 2 / P) -
          A * (thetaCuspHigherLikelihoodSpectralMoment B 1 / P) =
        (A ^ (6 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 6 -
          15 * A ^ (5 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 5 +
          65 * A ^ (4 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 4 -
          90 * A ^ (3 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 3 +
          31 * A ^ (2 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 2 -
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
  have he25 : 27 * e2 ≤ e5 := by linarith only [he23, he34, he45]
  have hmomentProduct : e2 * e3 ≤ p * e5 := by
    simpa only [B, p, e2, e3, e5, show 2 + 3 = 5 by norm_num] using
      thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 2 3
  have hfirst : 5 * m * e4 < e5 / 36 := by
    have hprod : 0 < (1 - 60 * m) * e4 := by positivity
    linarith only [hprod, he45]
  have hsecond : 10 * e2 * e3 < e5 / 18 := by
    have hprod : 0 < (1 - 180 * p) * e5 := by positivity
    linarith only [hprod, hmomentProduct]
  have hmOne : m < 1 := by linarith only [hmSmall]
  have hmSqOne : m ^ (2 : ℕ) < 1 := pow_lt_one₀ hm.le hmOne (by norm_num)
  have hmCube : m ^ (3 : ℕ) < m := by
    calc
      m ^ (3 : ℕ) = m * m ^ (2 : ℕ) := by ring
      _ < m * 1 := mul_lt_mul_of_pos_left hmSqOne hm
      _ = m := by ring
  have hthird : 60 * m ^ (3 : ℕ) * e2 < e5 / 27 := by
    have hcoef : 60 * m ^ (3 : ℕ) < 1 := by linarith only [hmCube, hmSmall]
    have hmul := mul_lt_mul_of_pos_right hcoef he2
    linarith only [hmul, he25]
  have hfirstA : 5 * A ^ (5 : ℕ) * m * e4 < A ^ (5 : ℕ) * e5 / 36 := by
    have hmul := mul_lt_mul_of_pos_left hfirst (pow_pos hA0 5)
    linarith only [hmul]
  have hsecondA : 10 * A ^ (5 : ℕ) * e2 * e3 < A ^ (5 : ℕ) * e5 / 18 := by
    have hmul := mul_lt_mul_of_pos_left hsecond (pow_pos hA0 5)
    linarith only [hmul]
  have hthirdA : 60 * A ^ (5 : ℕ) * m ^ (3 : ℕ) * e2 < A ^ (5 : ℕ) * e5 / 27 := by
    have hmul := mul_lt_mul_of_pos_left hthird (pow_pos hA0 5)
    linarith only [hmul]
  have hmSqSmall : 3600 * m ^ (2 : ℕ) < 1 := by
    have hprod : 0 < (1 - 60 * m) * (1 + 60 * m) := by positivity
    linarith only [hprod]
  have hcoefFour : 240000 * m ^ (2 : ℕ) < 200 / 3 := by linarith only [hmSqSmall]
  have hAe5 : 81 * e2 < A * e5 := by
    have hmul := mul_lt_mul_of_pos_right hA he5
    linarith only [hmul, he25]
  have hrawFour : 240000 * m ^ (2 : ℕ) * e2 < A * e5 := by
    have hmul := mul_lt_mul_of_pos_right hcoefFour he2
    linarith only [hmul, hAe5, he2]
  have hfourthA :
      120 * A ^ (4 : ℕ) * m ^ (2 : ℕ) * e2 < A ^ (5 : ℕ) * e5 / 2000 := by
    have hmul := mul_lt_mul_of_pos_left hrawFour (pow_pos hA0 4)
    calc
      120 * A ^ (4 : ℕ) * m ^ (2 : ℕ) * e2 =
          (A ^ (4 : ℕ) * (240000 * m ^ (2 : ℕ) * e2)) / 2000 := by ring
      _ < (A ^ (4 : ℕ) * (A * e5)) / 2000 :=
        div_lt_div_of_pos_right hmul (by norm_num)
      _ = A ^ (5 : ℕ) * e5 / 2000 := by ring
  have hcoefFive : 13500 * m < 225 := by linarith only [hmSmall]
  have hA_sq : 9 < A ^ (2 : ℕ) := by linarith only [hA, sq_nonneg (A - 3)]
  have hA2e5 : 243 * e2 < A ^ (2 : ℕ) * e5 := by
    have hmul := mul_lt_mul_of_pos_right hA_sq he5
    linarith only [hmul, he25]
  have hrawFive : 13500 * m * e2 < A ^ (2 : ℕ) * e5 := by
    have hmul := mul_lt_mul_of_pos_right hcoefFive he2
    linarith only [hmul, hA2e5, he2]
  have hfifthA :
      75 * A ^ (3 : ℕ) * m * e2 < A ^ (5 : ℕ) * e5 / 180 := by
    have hmul := mul_lt_mul_of_pos_left hrawFive (pow_pos hA0 3)
    calc
      75 * A ^ (3 : ℕ) * m * e2 =
          (A ^ (3 : ℕ) * (13500 * m * e2)) / 180 := by ring
      _ < (A ^ (3 : ℕ) * (A ^ (2 : ℕ) * e5)) / 180 :=
        div_lt_div_of_pos_right hmul (by norm_num)
      _ = A ^ (5 : ℕ) * e5 / 180 := by ring
  have hnegative :
      5 * A ^ (5 : ℕ) * m * e4 + 10 * A ^ (5 : ℕ) * e2 * e3 +
          60 * A ^ (5 : ℕ) * m ^ (3 : ℕ) * e2 + 120 * A ^ (4 : ℕ) * m ^ (2 : ℕ) * e2 +
          75 * A ^ (3 : ℕ) * m * e2 < A ^ (5 : ℕ) * e5 / 6 := by
    have hAe : 0 < A ^ (5 : ℕ) * e5 := mul_pos (pow_pos hA0 5) he5
    linarith only [hfirstA, hsecondA, hthirdA, hfourthA, hfifthA, hAe]
  have hlinear :
      (1 / 6 : ℝ) * A ^ (5 : ℕ) * e5 ≤
        A ^ (5 : ℕ) * e5 - 10 * A ^ (4 : ℕ) * e4 + 25 * A ^ (3 : ℕ) * e3 -
          15 * A ^ (2 : ℕ) * e2 + A * m := by
    simpa only [A, B, m, e2, e3, e4, e5] using
      one_sixth_mul_likelihoodSourceLinearFive_le hx
  have hpos1 : 0 ≤ 20 * A ^ (5 : ℕ) * m ^ (2 : ℕ) * e3 := by positivity
  have hpos2 : 0 ≤ 30 * A ^ (5 : ℕ) * m * e2 ^ (2 : ℕ) := by positivity
  have hpos3 : 0 ≤ 24 * A ^ (5 : ℕ) * m ^ (5 : ℕ) := by positivity
  have hpos4 : 0 ≤ 40 * A ^ (4 : ℕ) * m * e3 := by positivity
  have hpos5 : 0 ≤ 30 * A ^ (4 : ℕ) * e2 ^ (2 : ℕ) := by positivity
  have hpos6 : 0 ≤ 60 * A ^ (4 : ℕ) * m ^ (4 : ℕ) := by positivity
  have hpos7 : 0 ≤ 50 * A ^ (3 : ℕ) * m ^ (3 : ℕ) := by positivity
  have hpos8 : 0 ≤ 15 * A ^ (2 : ℕ) * m ^ (2 : ℕ) := by positivity
  dsimp only [A, B, m, e2, e3, e4, e5] at
    hnegative hlinear hpos1 hpos2 hpos3 hpos4 hpos5 hpos6 hpos7 hpos8
  unfold thetaCuspLikelihoodSourceLogPartitionJetFive
    thetaCuspLikelihoodFifthCumulant thetaCuspLikelihoodFourthCumulant
    thetaCuspLikelihoodThirdCumulant
  rw [thetaCuspLikelihoodVariance_eq_normalizedMoment_two_sub_mean_sq]
  unfold thetaCuspLikelihoodNormalizedMoment at
    hnegative hlinear hpos1 hpos2 hpos3 hpos4 hpos5 hpos6 hpos7 hpos8 ⊢
  linarith only [hnegative, hlinear, hpos1, hpos2, hpos3, hpos4, hpos5, hpos6, hpos7, hpos8]

end

end RHTower
