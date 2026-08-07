import GaloisForLFunctions.RHTower.HedenmalmThetaSquaredSeamPencil
import GaloisForLFunctions.RHTower.HedenmalmRootFluxModularCharge

/-!
# The thermal RH energy as compact theta boundary flux

The faithful reciprocal-square orientation energy is identified term by term with the square of
the canonically normalized boundary flux of the actual theta root mode.  A second identity places
that flux on the genuine nonzero eigenvector of the fixed compact theta source inverse.
-/

open Complex MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace RHTower

noncomputable section

open HedenmalmQuantile HedenmalmThetaSource

/-- Ordered root flux attached to one multiplicity-exact Xi divisor copy. -/
def thetaXiRootFlux (q : XiZeroCopy) : ℝ :=
  (∫ t in Ioo (0 : ℝ) 1,
    -(rootH thetaSource (xiSpectralPoint q) t)).re

/-- The positive root energy attached to the same divisor copy. -/
def thetaXiRootEnergy (q : XiZeroCopy) : ℝ :=
  thetaRootEnergy (xiSpectralPoint q)

theorem thetaXiRootEnergy_pos (q : XiZeroCopy) :
    0 < thetaXiRootEnergy q := by
  exact thetaRootEnergy_pos (thetaXiSpectralPoint_mem_sourceStrip q)
    (xiC_thetaSource_xiSpectralPoint_eq_zero q)

/-- The root flux reads the transverse spectral coordinate without loss. -/
theorem thetaXiRootFlux_eq (q : XiZeroCopy) :
    thetaXiRootFlux q =
      -(xiSpectralPoint q).im * thetaXiRootEnergy q := by
  exact rootFlux_identity_thetaSource
    (thetaXiSpectralPoint_mem_sourceStrip q)
    (xiC_thetaSource_xiSpectralPoint_eq_zero q)

/-- Imaginary reciprocal square in centered spectral coordinates. -/
theorem xiZeroCopyReciprocalSquare_im_eq_spectral (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im =
      -(2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im) /
        Complex.normSq (xiSpectralPoint q) ^ 2 := by
  rw [xiZeroCopyReciprocalSquare, pow_two]
  simp only [Complex.mul_im, Complex.inv_re, Complex.inv_im]
  ring

/-- Canonically normalized squared output of the theta root-flux observer. -/
def thetaXiNormalizedRootFluxTerm (q : XiZeroCopy) : ℝ :=
  (2 * (xiSpectralPoint q).re * thetaXiRootFlux q /
      (thetaXiRootEnergy q * Complex.normSq (xiSpectralPoint q) ^ 2)) ^ 2

/-- **Pointwise Frankenstein identity.**  The normalized theta flux is exactly the faithful
reciprocal-square transverse square. -/
theorem thetaXiNormalizedRootFluxTerm_eq (q : XiZeroCopy) :
    thetaXiNormalizedRootFluxTerm q =
      (xiZeroCopyReciprocalSquare q).im ^ 2 := by
  have hE : thetaXiRootEnergy q ≠ 0 := (thetaXiRootEnergy_pos q).ne'
  have hD : Complex.normSq (xiSpectralPoint q) ≠ 0 :=
    (Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)).ne'
  rw [thetaXiNormalizedRootFluxTerm, thetaXiRootFlux_eq,
    xiZeroCopyReciprocalSquare_im_eq_spectral]
  field_simp [hE, hD]

/-- Global compact-root flux energy. -/
def thetaXiNormalizedRootFluxEnergy : ℝ :=
  ∑' q : XiZeroCopy, thetaXiNormalizedRootFluxTerm q

theorem summable_thetaXiNormalizedRootFluxTerm :
    Summable thetaXiNormalizedRootFluxTerm :=
  summable_xiThermalOrientationTerm.congr fun q =>
    (thetaXiNormalizedRootFluxTerm_eq q).symm

/-- The new theta flux energy is exactly the established faithful thermal orientation energy. -/
theorem thetaXiNormalizedRootFluxEnergy_eq_thermalOrientationEnergy :
    thetaXiNormalizedRootFluxEnergy = xiThermalOrientationEnergy := by
  rw [thetaXiNormalizedRootFluxEnergy, xiThermalOrientationEnergy]
  exact tsum_congr thetaXiNormalizedRootFluxTerm_eq

theorem thetaXiNormalizedRootFluxEnergy_nonneg :
    0 ≤ thetaXiNormalizedRootFluxEnergy := by
  rw [thetaXiNormalizedRootFluxEnergy]
  exact tsum_nonneg fun q => sq_nonneg _

/-- Vanishing of the compact theta root-flux energy is exactly RH. -/
theorem thetaXiNormalizedRootFluxEnergy_eq_zero_iff_riemannHypothesis :
    thetaXiNormalizedRootFluxEnergy = 0 ↔ RiemannHypothesis := by
  rw [thetaXiNormalizedRootFluxEnergy_eq_thermalOrientationEnergy,
    xiThermalOrientationEnergy_eq_zero_iff_rh]

end

end RHTower
