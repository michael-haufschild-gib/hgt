import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMTotalRenormalizedAngularPeriod
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNonlinearRadiationKernel

/-!
# Nonlinear FE-reflection boundary producer

The FE-reflected and Schwarz-conjugated BM transfers define one folded boundary defect `d` at
common horizon amplitude.  Pairing the complete retarded `++-` angular periods on both sectors
gives `P` with strictly positive imaginary part.  The causal quarter-turn `-I * P` is therefore
strictly accretive.  The source-free nonlinear boundary current

`J(d) = d - I * P * normSq(d) * d`

has positive optical power away from `d = 0`; hence its stationary locus identifies the two
transfers.  Arbitrary conservative finite part cannot create a nonzero stationary branch.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Common-horizon FE/Schwarz boundary defect. -/
def d4BMXiFESchwarzFoldedBoundaryDefectAmplitude
    (q : XiZeroCopy) (horizon : ℂ) : ℂ :=
  (d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) -
    d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q)) * horizon

/-- Complete retarded `++-` period of both folded sectors. -/
def d4BMXiFESchwarzFoldedTotalRetardedPeriod
    (conservativeFinitePart : ℝ) (seed reflectedMixing conjugateMixing : ℂ)
    (q : XiZeroCopy) : ℂ :=
  d4BMXiGaugeFixedTotalRenormalizedAngularPeriod conservativeFinitePart
      seed reflectedMixing (xiZeroCopyReflectEquiv q) +
    d4BMXiGaugeFixedTotalRenormalizedAngularPeriod conservativeFinitePart
      seed conjugateMixing (xiZeroCopyConjEquiv q)

theorem d4BMXiFESchwarzFoldedTotalRetardedPeriod_im
    (conservativeFinitePart : ℝ) (seed reflectedMixing conjugateMixing : ℂ)
    (q : XiZeroCopy) :
    (d4BMXiFESchwarzFoldedTotalRetardedPeriod conservativeFinitePart seed
      reflectedMixing conjugateMixing q).im =
      d4BMXiGaugeFixedTotalAngularRadiationFlux seed reflectedMixing
          (xiZeroCopyReflectEquiv q) +
        d4BMXiGaugeFixedTotalAngularRadiationFlux seed conjugateMixing
          (xiZeroCopyConjEquiv q) := by
  simp [d4BMXiFESchwarzFoldedTotalRetardedPeriod,
    d4BMXiGaugeFixedTotalRenormalizedAngularPeriod_im]

/-- Nonzero theta seed makes the folded retarded period strictly dissipative. -/
theorem d4BMXiFESchwarzFoldedTotalRetardedPeriod_im_pos
    (conservativeFinitePart : ℝ) {seed : ℂ} (hseed : seed ≠ 0)
    (reflectedMixing conjugateMixing : ℂ) (q : XiZeroCopy) :
    0 < (d4BMXiFESchwarzFoldedTotalRetardedPeriod conservativeFinitePart seed
      reflectedMixing conjugateMixing q).im := by
  rw [d4BMXiFESchwarzFoldedTotalRetardedPeriod_im]
  exact add_pos
    (d4BMXiGaugeFixedTotalAngularRadiationFlux_pos hseed reflectedMixing _)
    (d4BMXiGaugeFixedTotalAngularRadiationFlux_pos hseed conjugateMixing _)

/-- Causal cubic boundary current of the folded FE/Schwarz channel. -/
def d4BMXiFESchwarzNonlinearBoundaryCurrent
    (conservativeFinitePart : ℝ) (seed reflectedMixing conjugateMixing : ℂ)
    (q : XiZeroCopy) (horizon : ℂ) : ℂ :=
  let d := d4BMXiFESchwarzFoldedBoundaryDefectAmplitude q horizon
  d - Complex.I *
      d4BMXiFESchwarzFoldedTotalRetardedPeriod conservativeFinitePart seed
        reflectedMixing conjugateMixing q *
      (Complex.normSq d : ℂ) * d

theorem d4BMXiFESchwarzNonlinearBoundaryCurrent_factor
    (conservativeFinitePart : ℝ) (seed reflectedMixing conjugateMixing : ℂ)
    (q : XiZeroCopy) (horizon : ℂ) :
    d4BMXiFESchwarzNonlinearBoundaryCurrent conservativeFinitePart seed
        reflectedMixing conjugateMixing q horizon =
      (1 - Complex.I *
          d4BMXiFESchwarzFoldedTotalRetardedPeriod conservativeFinitePart seed
            reflectedMixing conjugateMixing q *
          (Complex.normSq
            (d4BMXiFESchwarzFoldedBoundaryDefectAmplitude q horizon) : ℂ)) *
        d4BMXiFESchwarzFoldedBoundaryDefectAmplitude q horizon := by
  simp [d4BMXiFESchwarzNonlinearBoundaryCurrent]
  ring

theorem d4BMXiRetardedCubicBoundaryCoefficient_re
    (period defect : ℂ) :
    (1 - Complex.I * period * (Complex.normSq defect : ℂ)).re =
      1 + period.im * Complex.normSq defect := by
  simp [Complex.mul_re]

/-- Optical power is direct folded flux plus quartic total-period dissipation. -/
theorem d4BMXiRetardedCubicBoundaryPower_eq (period defect : ℂ) :
    (((starRingEnd ℂ) defect) *
      (defect - Complex.I * period * (Complex.normSq defect : ℂ) * defect)).re =
      Complex.normSq defect + period.im * Complex.normSq defect ^ (2 : ℕ) := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem d4BMXiFESchwarzNonlinearBoundaryCurrent_power_eq
    (conservativeFinitePart : ℝ) (seed reflectedMixing conjugateMixing : ℂ)
    (q : XiZeroCopy) (horizon : ℂ) :
    (((starRingEnd ℂ)
        (d4BMXiFESchwarzFoldedBoundaryDefectAmplitude q horizon)) *
      d4BMXiFESchwarzNonlinearBoundaryCurrent conservativeFinitePart seed
        reflectedMixing conjugateMixing q horizon).re =
      Complex.normSq (d4BMXiFESchwarzFoldedBoundaryDefectAmplitude q horizon) +
        (d4BMXiFESchwarzFoldedTotalRetardedPeriod conservativeFinitePart seed
          reflectedMixing conjugateMixing q).im *
          Complex.normSq
            (d4BMXiFESchwarzFoldedBoundaryDefectAmplitude q horizon) ^ (2 : ℕ) := by
  exact d4BMXiRetardedCubicBoundaryPower_eq _ _

/-- Every nonzero folded defect has strictly positive nonlinear boundary power. -/
theorem d4BMXiFESchwarzNonlinearBoundaryCurrent_power_pos
    (conservativeFinitePart : ℝ) {seed : ℂ} (hseed : seed ≠ 0)
    (reflectedMixing conjugateMixing : ℂ) (q : XiZeroCopy) (horizon : ℂ)
    (hdefect : d4BMXiFESchwarzFoldedBoundaryDefectAmplitude q horizon ≠ 0) :
    0 < (((starRingEnd ℂ)
        (d4BMXiFESchwarzFoldedBoundaryDefectAmplitude q horizon)) *
      d4BMXiFESchwarzNonlinearBoundaryCurrent conservativeFinitePart seed
        reflectedMixing conjugateMixing q horizon).re := by
  rw [d4BMXiFESchwarzNonlinearBoundaryCurrent_power_eq]
  have him := d4BMXiFESchwarzFoldedTotalRetardedPeriod_im_pos
    conservativeFinitePart hseed reflectedMixing conjugateMixing q
  have hnorm :
      0 < Complex.normSq
        (d4BMXiFESchwarzFoldedBoundaryDefectAmplitude q horizon) :=
    Complex.normSq_pos.mpr hdefect
  positivity

/-- Stationarity of the nonlinear current is exactly vanishing folded boundary defect. -/
theorem d4BMXiFESchwarzNonlinearBoundaryCurrent_eq_zero_iff_defect_eq_zero
    (conservativeFinitePart : ℝ) {seed : ℂ} (hseed : seed ≠ 0)
    (reflectedMixing conjugateMixing : ℂ) (q : XiZeroCopy) (horizon : ℂ) :
    d4BMXiFESchwarzNonlinearBoundaryCurrent conservativeFinitePart seed
        reflectedMixing conjugateMixing q horizon = 0 ↔
      d4BMXiFESchwarzFoldedBoundaryDefectAmplitude q horizon = 0 := by
  rw [d4BMXiFESchwarzNonlinearBoundaryCurrent_factor]
  let coefficient : ℂ :=
    1 - Complex.I *
      d4BMXiFESchwarzFoldedTotalRetardedPeriod conservativeFinitePart seed
        reflectedMixing conjugateMixing q *
      (Complex.normSq
        (d4BMXiFESchwarzFoldedBoundaryDefectAmplitude q horizon) : ℂ)
  have him :
      0 < (d4BMXiFESchwarzFoldedTotalRetardedPeriod conservativeFinitePart seed
        reflectedMixing conjugateMixing q).im :=
    d4BMXiFESchwarzFoldedTotalRetardedPeriod_im_pos conservativeFinitePart
      hseed reflectedMixing conjugateMixing q
  have hreal : 0 < coefficient.re := by
    rw [show coefficient.re = 1 +
        (d4BMXiFESchwarzFoldedTotalRetardedPeriod conservativeFinitePart seed
          reflectedMixing conjugateMixing q).im *
        Complex.normSq
          (d4BMXiFESchwarzFoldedBoundaryDefectAmplitude q horizon) by
      exact d4BMXiRetardedCubicBoundaryCoefficient_re _ _]
    nlinarith [Complex.normSq_nonneg
      (d4BMXiFESchwarzFoldedBoundaryDefectAmplitude q horizon)]
  have hcoefficient : coefficient ≠ 0 := by
    intro hzero
    have := congrArg Complex.re hzero
    simp [hzero] at hreal
  change coefficient *
    d4BMXiFESchwarzFoldedBoundaryDefectAmplitude q horizon = 0 ↔ _
  simp [hcoefficient]

/-- Source-free nonlinear boundary dynamics identify FE-reflected and Schwarz transfers. -/
theorem d4BMXiFESchwarzNonlinearBoundaryCurrent_eq_zero_iff_transfer_eq
    (conservativeFinitePart : ℝ) {seed : ℂ} (hseed : seed ≠ 0)
    (reflectedMixing conjugateMixing : ℂ) (q : XiZeroCopy)
    {horizon : ℂ} (hhorizon : horizon ≠ 0) :
    d4BMXiFESchwarzNonlinearBoundaryCurrent conservativeFinitePart seed
        reflectedMixing conjugateMixing q horizon = 0 ↔
      d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) =
        d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q) := by
  rw [d4BMXiFESchwarzNonlinearBoundaryCurrent_eq_zero_iff_defect_eq_zero
    conservativeFinitePart hseed reflectedMixing conjugateMixing q horizon]
  unfold d4BMXiFESchwarzFoldedBoundaryDefectAmplitude
  rw [mul_eq_zero]
  simp only [hhorizon, or_false]
  exact sub_eq_zero

end

end RHTower
