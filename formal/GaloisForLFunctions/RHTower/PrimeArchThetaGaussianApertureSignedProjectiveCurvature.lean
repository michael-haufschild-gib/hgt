import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureTwoChannelTransport

/-!
# Signed projective curvature of the first theta atom

The positive `p = 4` channel does not carry the required curvature throughout the physical
Gaussian-aperture chamber: its cold-aperture curvature is eventually negative.  The sign is
repaired by the literal signed `p = 2` correction.  This file keeps that cancellation exact.

The new object is the adjacent projective minor of the positive amplitude factors.  Clearing the
three positive denominators converts the signed curvature correction into a difference of two
neighboring projective fluxes.  Unlike the absolute-value leakage estimate, this identity loses no
order and no sign information.
-/

open Real

namespace RHTower

noncomputable section

/-- Adjacent projective minor of the signed first-atom amplitude factors. -/
def thetaCuspGaussianApertureTailAmplitudeProjectiveMinor
    (lambda : ℝ) (j : ℕ) : ℝ :=
  thetaCuspGaussianApertureTailAmplitudeFactor lambda (j + 1) ^ 2 -
    thetaCuspGaussianApertureTailAmplitudeFactor lambda j *
      thetaCuspGaussianApertureTailAmplitudeFactor lambda (j + 2)

/-- Exact expression of the amplitude minor in the correction-ratio coordinates.  The first term
is an additive second difference; the second is a multiplicative Turán minor. -/
theorem thetaCuspGaussianApertureTailAmplitudeProjectiveMinor_eq_correctionRatio
    (lambda : ℝ) (j : ℕ) :
    thetaCuspGaussianApertureTailAmplitudeProjectiveMinor lambda j =
      (3 / (2 * Real.pi)) *
          (thetaCuspGaussianApertureTailCorrectionRatio lambda j -
            2 * thetaCuspGaussianApertureTailCorrectionRatio lambda (j + 1) +
            thetaCuspGaussianApertureTailCorrectionRatio lambda (j + 2)) +
        (3 / (2 * Real.pi)) ^ 2 *
          (thetaCuspGaussianApertureTailCorrectionRatio lambda (j + 1) ^ 2 -
            thetaCuspGaussianApertureTailCorrectionRatio lambda j *
              thetaCuspGaussianApertureTailCorrectionRatio lambda (j + 2)) := by
  unfold thetaCuspGaussianApertureTailAmplitudeProjectiveMinor
    thetaCuspGaussianApertureTailAmplitudeFactor
  ring

/-- The part of the literal first-atom curvature produced by the signed amplitude correction,
after subtracting the transported `p = 4` channel curvature. -/
def thetaCuspGaussianApertureSignedAmplitudeCurvatureCorrection
    (lambda : ℝ) (j : ℕ) : ℝ :=
  thetaCuspGaussianApertureFirstAtomRatioCurvature lambda j -
    thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 1) *
      thetaCuspGaussianApertureTailChannelRatioCurvature lambda 4 j

/-- The signed correction is the weighted second difference of the amplitude multiplier.  This is
the denominator-free form most directly exposed to the source score calculus. -/
theorem thetaCuspGaussianApertureSignedAmplitudeCurvatureCorrection_eq_weightedDecrements
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureSignedAmplitudeCurvatureCorrection lambda j =
      thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 j *
          (thetaCuspGaussianApertureTailAmplitudeMultiplier lambda j -
            thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 1)) -
        thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 (j + 2) *
          (thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 1) -
            thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 2)) := by
  rw [thetaCuspGaussianApertureSignedAmplitudeCurvatureCorrection,
    thetaCuspGaussianApertureFirstAtomRatioCurvature_eq_transport hlambda]
  ring

/-- The open signed-curvature producer is exactly a weighted concavity law for the amplitude
multiplier sequence. -/
theorem thetaCuspGaussianApertureSignedAmplitudeCurvatureCorrection_nonneg_iff_weightedDecrements
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    0 ≤ thetaCuspGaussianApertureSignedAmplitudeCurvatureCorrection lambda j ↔
      thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 (j + 2) *
          (thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 1) -
            thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 2)) ≤
        thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 j *
          (thetaCuspGaussianApertureTailAmplitudeMultiplier lambda j -
            thetaCuspGaussianApertureTailAmplitudeMultiplier lambda (j + 1)) := by
  rw [thetaCuspGaussianApertureSignedAmplitudeCurvatureCorrection_eq_weightedDecrements
    hlambda]
  constructor <;> intro h <;> linarith

/-- Denominator-free signed projective transport law.  It is the exact cancellation-preserving
replacement for the absolute-value leakage bound. -/
theorem thetaCuspGaussianApertureSignedAmplitudeCurvatureCorrection_mul_factors
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureTailAmplitudeFactor lambda j *
        thetaCuspGaussianApertureTailAmplitudeFactor lambda (j + 1) *
        thetaCuspGaussianApertureTailAmplitudeFactor lambda (j + 2) *
        thetaCuspGaussianApertureSignedAmplitudeCurvatureCorrection lambda j =
      thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 j *
          thetaCuspGaussianApertureTailAmplitudeFactor lambda (j + 2) *
          thetaCuspGaussianApertureTailAmplitudeProjectiveMinor lambda j -
        thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 (j + 2) *
          thetaCuspGaussianApertureTailAmplitudeFactor lambda j *
          thetaCuspGaussianApertureTailAmplitudeProjectiveMinor lambda (j + 1) := by
  rw [thetaCuspGaussianApertureSignedAmplitudeCurvatureCorrection,
    thetaCuspGaussianApertureFirstAtomRatioCurvature_eq_transport hlambda]
  unfold thetaCuspGaussianApertureTailAmplitudeMultiplier
    thetaCuspGaussianApertureTailAmplitudeProjectiveMinor
  have hd0 :=
    (thetaCuspGaussianApertureTailAmplitudeFactor_pos hlambda j).ne'
  have hd1 :=
    (thetaCuspGaussianApertureTailAmplitudeFactor_pos hlambda (j + 1)).ne'
  have hd2 :=
    (thetaCuspGaussianApertureTailAmplitudeFactor_pos hlambda (j + 2)).ne'
  field_simp [hd0, hd1, hd2]
  ring

/-- The literal signed correction has nonnegative curvature exactly when the left projective flux
dominates its adjacent right flux.  This is the source-specific global inequality still open after
the cold-aperture sign reversal. -/
theorem thetaCuspGaussianApertureSignedAmplitudeCurvatureCorrection_nonneg_iff
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    0 ≤ thetaCuspGaussianApertureSignedAmplitudeCurvatureCorrection lambda j ↔
      thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 (j + 2) *
            thetaCuspGaussianApertureTailAmplitudeFactor lambda j *
            thetaCuspGaussianApertureTailAmplitudeProjectiveMinor lambda (j + 1) ≤
        thetaCuspGaussianApertureTailChannelGammaRatio lambda 4 j *
            thetaCuspGaussianApertureTailAmplitudeFactor lambda (j + 2) *
            thetaCuspGaussianApertureTailAmplitudeProjectiveMinor lambda j := by
  let dprod :=
    thetaCuspGaussianApertureTailAmplitudeFactor lambda j *
      thetaCuspGaussianApertureTailAmplitudeFactor lambda (j + 1) *
      thetaCuspGaussianApertureTailAmplitudeFactor lambda (j + 2)
  have hdprod : 0 < dprod := by
    dsimp only [dprod]
    exact mul_pos
      (mul_pos
        (thetaCuspGaussianApertureTailAmplitudeFactor_pos hlambda j)
        (thetaCuspGaussianApertureTailAmplitudeFactor_pos hlambda (j + 1)))
      (thetaCuspGaussianApertureTailAmplitudeFactor_pos hlambda (j + 2))
  have hflux :=
    thetaCuspGaussianApertureSignedAmplitudeCurvatureCorrection_mul_factors
      hlambda j
  change 0 ≤ thetaCuspGaussianApertureSignedAmplitudeCurvatureCorrection lambda j ↔ _
  rw [← (mul_nonneg_iff_of_pos_left hdprod)]
  change 0 ≤ dprod *
      thetaCuspGaussianApertureSignedAmplitudeCurvatureCorrection lambda j ↔ _
  rw [hflux]
  constructor <;> intro h <;> linarith

/-- Exact positive cold-amplitude coefficient exposed by the signed `p = 2` correction. -/
def thetaCuspGaussianApertureColdSignedCorrectionCoefficient : ℝ :=
  6 / (2 * Real.pi - 3)

theorem thetaCuspGaussianApertureColdSignedCorrectionCoefficient_pos :
    0 < thetaCuspGaussianApertureColdSignedCorrectionCoefficient := by
  rw [thetaCuspGaussianApertureColdSignedCorrectionCoefficient]
  have hden : 0 < 2 * Real.pi - 3 := by
    nlinarith [Real.pi_gt_three]
  positivity

/-- The bad cold `p = 4` boundary slope plus the signed correction is exactly the already-positive
boundary logarithmic slope of the literal first theta atom. -/
theorem thetaCuspGaussianAperture_coldSlope_signFlip :
    9 / 2 - 2 * Real.pi +
        thetaCuspGaussianApertureColdSignedCorrectionCoefficient =
      thetaCuspFirstAtomBoundaryLogSlope := by
  rfl

theorem thetaCuspGaussianAperture_coldSlope_signFlip_pos :
    0 < 9 / 2 - 2 * Real.pi +
        thetaCuspGaussianApertureColdSignedCorrectionCoefficient := by
  rw [thetaCuspGaussianAperture_coldSlope_signFlip]
  exact thetaCuspFirstAtomBoundaryLogSlope_pos

/-! ### Exact all-degree sign of the cold half-order coefficient -/

/-- The Gamma quotient multiplying the first half-order Watson correction at degree `j`. -/
def thetaCuspGaussianApertureColdHalfOrderGammaGap (j : ℕ) : ℝ :=
  Real.Gamma ((j : ℝ) + 1) /
    ((2 * (j : ℝ) + 1) * Real.Gamma ((j : ℝ) + 1 / 2))

theorem thetaCuspGaussianApertureColdHalfOrderGammaGap_pos (j : ℕ) :
    0 < thetaCuspGaussianApertureColdHalfOrderGammaGap j := by
  rw [thetaCuspGaussianApertureColdHalfOrderGammaGap]
  exact div_pos
    (Real.Gamma_pos_of_pos (by positivity))
    (mul_pos (by positivity) (Real.Gamma_pos_of_pos (by positivity)))

/-- The half-order Gamma gap has an exact rational degree recurrence. -/
theorem thetaCuspGaussianApertureColdHalfOrderGammaGap_succ (j : ℕ) :
    thetaCuspGaussianApertureColdHalfOrderGammaGap (j + 1) =
      ((2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3)) *
        thetaCuspGaussianApertureColdHalfOrderGammaGap j := by
  rw [thetaCuspGaussianApertureColdHalfOrderGammaGap,
    thetaCuspGaussianApertureColdHalfOrderGammaGap]
  rw [show ((j + 1 : ℕ) : ℝ) + 1 = ((j : ℝ) + 1) + 1 by
      norm_num [Nat.cast_add, Nat.cast_one],
    Real.Gamma_add_one (by positivity : (j : ℝ) + 1 ≠ 0)]
  rw [show ((j + 1 : ℕ) : ℝ) + 1 / 2 = ((j : ℝ) + 1 / 2) + 1 by
      norm_num [Nat.cast_add, Nat.cast_one]
      ring,
    Real.Gamma_add_one (by positivity : (j : ℝ) + 1 / 2 ≠ 0)]
  have hgamma : Real.Gamma ((j : ℝ) + 1 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp [hgamma]
  ring

/-- The discrete curvature of the cold half-order coefficient is exactly positive in every
degree.  This is the all-degree factor shared by the bad `p = 4` slope and the sign-reversing
literal first-atom slope. -/
theorem thetaCuspGaussianApertureColdHalfOrderGammaGap_secondDiff (j : ℕ) :
    thetaCuspGaussianApertureColdHalfOrderGammaGap j -
        2 * thetaCuspGaussianApertureColdHalfOrderGammaGap (j + 1) +
        thetaCuspGaussianApertureColdHalfOrderGammaGap (j + 2) =
      3 * thetaCuspGaussianApertureColdHalfOrderGammaGap j /
        ((2 * (j : ℝ) + 3) * (2 * (j : ℝ) + 5)) := by
  have h1 := thetaCuspGaussianApertureColdHalfOrderGammaGap_succ j
  have h2 := thetaCuspGaussianApertureColdHalfOrderGammaGap_succ (j + 1)
  rw [h1, h2, h1]
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem thetaCuspGaussianApertureColdHalfOrderGammaGap_secondDiff_pos (j : ℕ) :
    0 < thetaCuspGaussianApertureColdHalfOrderGammaGap j -
        2 * thetaCuspGaussianApertureColdHalfOrderGammaGap (j + 1) +
        thetaCuspGaussianApertureColdHalfOrderGammaGap (j + 2) := by
  rw [thetaCuspGaussianApertureColdHalfOrderGammaGap_secondDiff]
  exact div_pos
    (mul_pos (by norm_num)
      (thetaCuspGaussianApertureColdHalfOrderGammaGap_pos j))
    (mul_pos (by positivity) (by positivity))

/-- The leading positive `p = 4` channel has the wrong cold half-order sign in every degree. -/
theorem thetaCuspGaussianAperture_coldLeadingSlopeCoefficient_neg (j : ℕ) :
    (9 / 2 - 2 * Real.pi) *
        (thetaCuspGaussianApertureColdHalfOrderGammaGap j -
          2 * thetaCuspGaussianApertureColdHalfOrderGammaGap (j + 1) +
          thetaCuspGaussianApertureColdHalfOrderGammaGap (j + 2)) < 0 := by
  exact mul_neg_of_neg_of_pos
    (by nlinarith [Real.pi_gt_three])
    (thetaCuspGaussianApertureColdHalfOrderGammaGap_secondDiff_pos j)

/-- The signed `p = 2` correction has the opposite, strictly positive cold coefficient in every
degree. -/
theorem thetaCuspGaussianAperture_coldSignedCorrectionCoefficient_pos (j : ℕ) :
    0 < thetaCuspGaussianApertureColdSignedCorrectionCoefficient *
        (thetaCuspGaussianApertureColdHalfOrderGammaGap j -
          2 * thetaCuspGaussianApertureColdHalfOrderGammaGap (j + 1) +
          thetaCuspGaussianApertureColdHalfOrderGammaGap (j + 2)) := by
  exact mul_pos
    thetaCuspGaussianApertureColdSignedCorrectionCoefficient_pos
    (thetaCuspGaussianApertureColdHalfOrderGammaGap_secondDiff_pos j)

/-- After the signed correction is restored, the literal first-atom cold coefficient is strictly
positive in every degree. -/
theorem thetaCuspGaussianAperture_coldFirstAtomSlopeCoefficient_pos (j : ℕ) :
    0 < thetaCuspFirstAtomBoundaryLogSlope *
        (thetaCuspGaussianApertureColdHalfOrderGammaGap j -
          2 * thetaCuspGaussianApertureColdHalfOrderGammaGap (j + 1) +
          thetaCuspGaussianApertureColdHalfOrderGammaGap (j + 2)) := by
  exact mul_pos thetaCuspFirstAtomBoundaryLogSlope_pos
    (thetaCuspGaussianApertureColdHalfOrderGammaGap_secondDiff_pos j)

end

end RHTower
