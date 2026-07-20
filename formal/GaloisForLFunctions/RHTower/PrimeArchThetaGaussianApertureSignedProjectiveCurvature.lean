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

end

end RHTower
