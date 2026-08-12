import GaloisForLFunctions.RHTower.HedenmalmThetaPhysicalEndpointHardyGreenResidualBridge
import GaloisForLFunctions.RHTower.OrbitSensitiveContinuationCharge

/-!
# Route P symmetric-quartet Hardy--Green no-go

Height phases are the next possible source of cancellation after scalar radial renormalization
fails.  For the actual conjugate right-half pair, however, the Cauchy cross-kernel is strictly
positive.  The symmetric-quartet energy is exactly twice the one-copy Route P residual energy plus
a strictly positive height-sensitive term.  Every exceptional quartet therefore costs more than
eight units.

Functional-equation/conjugation assembly with positive divisor multiplicities amplifies the
exceptional mode; it cannot cancel it.  A surviving entire-source mechanism must introduce a
signed pre-divisor coefficient or annihilate the exceptional mode before the positive Cauchy Gram
completion.
-/

open MeasureTheory Set

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Cauchy-Gram energy of the conjugate right-half pair attached to one Xi copy. -/
def thetaPhysicalEndpointSymmetricQuartetHardyGreenEnergy
    (q : XiZeroCopy) : ℝ :=
  finiteOfflineCauchyEnergy
    (symmetricQuartetDepth |(xiSpectralPoint q).im|)
    (symmetricQuartetHeight (xiSpectralPoint q).re)
    (symmetricQuartetMultiplicity 1)

/-- Exact decomposition into two Route P self-energies and a positive height cross-term. -/
theorem thetaPhysicalEndpointSymmetricQuartetHardyGreenEnergy_eq
    (q : XiZeroCopy)
    (h : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    thetaPhysicalEndpointSymmetricQuartetHardyGreenEnergy q =
      2 * (∫ x in Ioi (0 : ℝ),
        thetaPhysicalEndpointHardyGreenResidual q x ^ 2) +
      4 * |(xiSpectralPoint q).im| /
        (|(xiSpectralPoint q).im| ^ 2 + (xiSpectralPoint q).re ^ 2) := by
  have him : (xiSpectralPoint q).im ≠ 0 := by
    intro him
    apply h
    rw [primeDepthBVWoldXiCenteredRate_eq_neg_two_spectralIm, him]
    norm_num
  have ha : 0 < |(xiSpectralPoint q).im| := abs_pos.mpr him
  rw [thetaPhysicalEndpointSymmetricQuartetHardyGreenEnergy,
    symmetricQuartet_cauchyEnergy ha,
    integral_sq_thetaPhysicalEndpointHardyGreenResidual_eq_exceptionalHardyGreenEnergy q h,
    GaloisForLFunctions.exceptionalHardyGreenEnergy]
  field_simp [ha.ne']
  ring

/-- Conjugate height coherence strictly amplifies rather than cancels residual energy. -/
theorem two_mul_integral_sq_thetaPhysicalEndpointHardyGreenResidual_lt_quartetEnergy
    (q : XiZeroCopy)
    (h : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    2 * (∫ x in Ioi (0 : ℝ),
      thetaPhysicalEndpointHardyGreenResidual q x ^ 2) <
      thetaPhysicalEndpointSymmetricQuartetHardyGreenEnergy q := by
  rw [thetaPhysicalEndpointSymmetricQuartetHardyGreenEnergy_eq q h]
  have him : (xiSpectralPoint q).im ≠ 0 := by
    intro him
    apply h
    rw [primeDepthBVWoldXiCenteredRate_eq_neg_two_spectralIm, him]
    norm_num
  have ha : 0 < |(xiSpectralPoint q).im| := abs_pos.mpr him
  have hden : 0 < |(xiSpectralPoint q).im| ^ 2 +
      (xiSpectralPoint q).re ^ 2 := by positivity
  have hterm : 0 < 4 * |(xiSpectralPoint q).im| /
      (|(xiSpectralPoint q).im| ^ 2 + (xiSpectralPoint q).re ^ 2) :=
    div_pos (mul_pos (by norm_num) ha) hden
  linarith

/-- Every exceptional Xi quartet has Cauchy-Gram energy strictly greater than eight. -/
theorem eight_lt_thetaPhysicalEndpointSymmetricQuartetHardyGreenEnergy
    (q : XiZeroCopy)
    (h : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    8 < thetaPhysicalEndpointSymmetricQuartetHardyGreenEnergy q := by
  have htwo :=
    two_mul_integral_sq_thetaPhysicalEndpointHardyGreenResidual_lt_quartetEnergy q h
  have hone := four_lt_integral_sq_thetaPhysicalEndpointHardyGreenResidual q h
  linarith

/-- Neutral copies carry zero quartet energy. -/
theorem thetaPhysicalEndpointSymmetricQuartetHardyGreenEnergy_eq_zero_of_boundaryFlux_zero
    (q : XiZeroCopy) (hflux : thetaXiRankTwoBoundaryFlux q = 0) :
    thetaPhysicalEndpointSymmetricQuartetHardyGreenEnergy q = 0 := by
  have him :=
    (thetaXiRankTwoBoundaryFlux_eq_zero_iff_spectralIm_eq_zero q).mp hflux
  rw [thetaPhysicalEndpointSymmetricQuartetHardyGreenEnergy, him]
  simp [finiteOfflineCauchyEnergy, symmetricQuartetDepth,
    symmetricQuartetHeight, symmetricQuartetMultiplicity, transverseCauchyKernel]

/-- Positive-quartet eight-unit source contract. -/
def ThetaPhysicalEndpointSymmetricQuartetHardyGreenEightBound : Prop :=
  ∀ q : XiZeroCopy,
    thetaPhysicalEndpointSymmetricQuartetHardyGreenEnergy q ≤ 8

/-- Global eight-unit quartet control is exactly RH. -/
theorem thetaPhysicalEndpointSymmetricQuartetHardyGreenEightBound_iff_riemannHypothesis :
    ThetaPhysicalEndpointSymmetricQuartetHardyGreenEightBound ↔ RiemannHypothesis := by
  rw [← thetaGreenBoundaryNeutral_iff_riemannHypothesis]
  constructor
  · intro hbound q
    by_contra hflux
    have him : (xiSpectralPoint q).im ≠ 0 := by
      exact fun him => hflux
        ((thetaXiRankTwoBoundaryFlux_eq_zero_iff_spectralIm_eq_zero q).mpr him)
    have hrate : primeDepthBVWoldXiCenteredRate q.1 ≠ 0 := by
      rw [primeDepthBVWoldXiCenteredRate_eq_neg_two_spectralIm]
      exact mul_ne_zero (by norm_num) him
    exact (not_lt_of_ge (hbound q))
      (eight_lt_thetaPhysicalEndpointSymmetricQuartetHardyGreenEnergy q hrate)
  · intro hneutral q
    rw [thetaPhysicalEndpointSymmetricQuartetHardyGreenEnergy_eq_zero_of_boundaryFlux_zero
      q (hneutral q)]
    norm_num

end

end RHTower.HedenmalmThetaSource
