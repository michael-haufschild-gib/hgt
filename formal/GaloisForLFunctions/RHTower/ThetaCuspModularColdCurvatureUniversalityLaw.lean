import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodModularFluctuation
import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureSignedProjectiveCurvature

/-!
# Modular fluctuation cone for every cold theta-curvature degree

The signed Gaussian-aperture correction converts the bad cold slope into the literal first-atom
boundary slope.  Independently, that same slope lies strictly inside the modular likelihood moment
cone.  Multiplying by the positive all-degree half-order Gamma curvature transports the strict
modular fluctuation to every cold projective-curvature degree.
-/

namespace RHTower

noncomputable section

/-- Positive all-degree half-order Gamma curvature factor. -/
def thetaCuspModularColdCurvatureFactor (j : ℕ) : ℝ :=
  thetaCuspGaussianApertureColdHalfOrderGammaGap j -
    2 * thetaCuspGaussianApertureColdHalfOrderGammaGap (j + 1) +
    thetaCuspGaussianApertureColdHalfOrderGammaGap (j + 2)

theorem thetaCuspModularColdCurvatureFactor_pos (j : ℕ) :
    0 < thetaCuspModularColdCurvatureFactor j := by
  exact thetaCuspGaussianApertureColdHalfOrderGammaGap_secondDiff_pos j

/-- Signed-corrected cold slope coefficient at degree `j`. -/
def thetaCuspModularColdSignedSlopeCoefficient (j : ℕ) : ℝ :=
  (9 / 2 - 2 * Real.pi +
      thetaCuspGaussianApertureColdSignedCorrectionCoefficient) *
    thetaCuspModularColdCurvatureFactor j

/-- The signed coefficient is exactly the modular first-atom slope times the positive Gamma
curvature factor. -/
theorem thetaCuspModularColdSignedSlopeCoefficient_eq_firstAtom (j : ℕ) :
    thetaCuspModularColdSignedSlopeCoefficient j =
      thetaCuspFirstAtomBoundaryLogSlope *
        thetaCuspModularColdCurvatureFactor j := by
  rw [thetaCuspModularColdSignedSlopeCoefficient,
    thetaCuspGaussianAperture_coldSlope_signFlip]

theorem thetaCuspModularColdSignedSlopeCoefficient_pos (j : ℕ) :
    0 < thetaCuspModularColdSignedSlopeCoefficient j := by
  rw [thetaCuspModularColdSignedSlopeCoefficient_eq_firstAtom]
  exact mul_pos thetaCuspFirstAtomBoundaryLogSlope_pos
    (thetaCuspModularColdCurvatureFactor_pos j)

/-- **All-degree modular cold-curvature fluctuation law.**  Every signed-corrected cold curvature
coefficient lies strictly inside the likelihood order-two moment cone, scaled by the square of its
positive half-order Gamma curvature factor. -/
theorem thetaCuspModularColdSignedSlope_strictFluctuation (j : ℕ) :
    thetaCuspModularColdSignedSlopeCoefficient j ^ 2 *
          (1 + thetaCuspHigherLikelihoodSpectralMoment
            (thetaCuspLikelihoodCoordinate 0) 0) ^ 2 <
      (2 * Real.pi) ^ 2 * thetaCuspModularColdCurvatureFactor j ^ 2 *
        thetaCuspHigherLikelihoodSpectralMoment
          (thetaCuspLikelihoodCoordinate 0) 0 *
        thetaCuspHigherLikelihoodSpectralMoment
          (thetaCuspLikelihoodCoordinate 0) 2 := by
  rw [thetaCuspModularColdSignedSlopeCoefficient_eq_firstAtom]
  have hscaled := mul_lt_mul_of_pos_right
    thetaCuspLikelihoodModularSeam_strictFluctuation
    (sq_pos_of_pos (thetaCuspModularColdCurvatureFactor_pos j))
  convert hscaled using 1 <;> first | rfl | ring

end

end RHTower
