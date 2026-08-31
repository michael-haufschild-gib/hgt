import GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEPeripheralSpectrumZeroModeRigidity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingCubicPhaseCovarianceOpticalNoGo

/-!
# HB phase-blind threshold-spectrum no-go

The ordinary peripheral HB completion consists of strictly damped finite-variation modes, an
absolutely continuous real-axis continuum, and a zero-frequency threshold atom.  The first two
parts vanish at late time, leaving exactly the atom.  This file combines that terminal-value law
with cubic AIME seed-phase covariance.

The two half-turn seed sectors are allowed completely unrelated transient spectra, densities,
measures, and carrier types.  If both full pole numerators cancel asymptotically, their threshold
atoms must differ by exactly twice the nonzero cubic AIME numerator.  Therefore one phase-blind
threshold atom cannot cancel both sectors.

This kills every source-independent finite-variation-plus-threshold realization of the remaining
HB radiative `++` producer.  The sharp survivor is a source-adapted zero mode carrying the odd
cubic phase charge, or a genuinely singular non-Rajchman/infinite-variation peripheral spectrum.

`[NEW] [HB] [AIME] [THRESHOLD] [PHASE TOMOGRAPHY] [ROUTE KILL] [LEAN-PROVED]`
-/

open Complex Real Set Filter Topology MeasureTheory

namespace RHTower

noncomputable section

/-- Peripheral spectral completion with arbitrary seed amplitude but a phase-blind passive
stationary term and threshold atom. -/
def d4BMPassivePeripheralSpectralPhaseFullPoleNumerator
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (dampedDensity dampedFrequency : Omega → ℂ)
    (boundaryDensity : ℝ → ℂ) (zeroMode amplitude : ℂ)
    (absorbedMass : NNReal) (q : XiZeroCopy) (delay : ℝ) : ℂ :=
  d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) +
    d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q) +
    d4BMPeripheralSpectralSourceRemainder
      mu dampedDensity dampedFrequency boundaryDensity zeroMode delay

/-- Every such phase-sector response converges to AIME plus the common passive/threshold part. -/
theorem d4BMPassivePeripheralSpectralPhaseFullPoleNumerator_tendsto
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (dampedDensity dampedFrequency : Omega → ℂ)
    (boundaryDensity : ℝ → ℂ) (zeroMode amplitude : ℂ)
    (hdampedDensity : Integrable dampedDensity mu)
    (hdampedFrequency : Measurable dampedFrequency)
    (hdamped : ∀ᵐ x ∂mu, (dampedFrequency x).im < 0)
    (hboundary : Integrable boundaryDensity)
    (absorbedMass : NNReal) (q : XiZeroCopy) :
    Tendsto
      (d4BMPassivePeripheralSpectralPhaseFullPoleNumerator
        mu dampedDensity dampedFrequency boundaryDensity zeroMode amplitude absorbedMass q)
      atTop
      (𝓝 (d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) +
        d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q) + zeroMode)) := by
  unfold d4BMPassivePeripheralSpectralPhaseFullPoleNumerator
  simpa using tendsto_const_nhds.add
    (d4BMPeripheralSpectralSourceRemainder_tendsto_zeroMode
      mu dampedDensity dampedFrequency boundaryDensity zeroMode
      hdampedDensity hdampedFrequency hdamped hboundary)

/-- Asymptotic cancellation forces the exact phase-dependent threshold coefficient. -/
theorem d4BMPassivePeripheralSpectralPhaseFullPoleNumerator_tendsto_zero_iff_zeroMode
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (dampedDensity dampedFrequency : Omega → ℂ)
    (boundaryDensity : ℝ → ℂ) (zeroMode amplitude : ℂ)
    (hdampedDensity : Integrable dampedDensity mu)
    (hdampedFrequency : Measurable dampedFrequency)
    (hdamped : ∀ᵐ x ∂mu, (dampedFrequency x).im < 0)
    (hboundary : Integrable boundaryDensity)
    (absorbedMass : NNReal) (q : XiZeroCopy) :
    Tendsto
        (d4BMPassivePeripheralSpectralPhaseFullPoleNumerator
          mu dampedDensity dampedFrequency boundaryDensity zeroMode amplitude absorbedMass q)
        atTop (𝓝 0) ↔
      zeroMode =
        -(d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) +
          d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q)) := by
  have hlimit := d4BMPassivePeripheralSpectralPhaseFullPoleNumerator_tendsto
    mu dampedDensity dampedFrequency boundaryDensity zeroMode amplitude
    hdampedDensity hdampedFrequency hdamped hboundary absorbedMass q
  constructor
  · intro hzero
    have heq := tendsto_nhds_unique hlimit hzero
    exact eq_neg_of_add_eq_zero_right heq
  · intro hzeroMode
    convert hlimit using 1
    rw [hzeroMode]
    ring

/-- Sharp survivor: successful opposite-phase completions force the odd threshold jump to equal
twice the physical cubic AIME numerator, regardless of either transient spectrum. -/
theorem d4BMPassivePeripheralSpectral_halfTurnCancellation_forces_zeroModeJump
    {OmegaPlus OmegaMinus : Type*}
    [MeasurableSpace OmegaPlus] [MeasurableSpace OmegaMinus]
    (muPlus : Measure OmegaPlus)
    (dampedDensityPlus dampedFrequencyPlus : OmegaPlus → ℂ)
    (boundaryDensityPlus : ℝ → ℂ)
    (muMinus : Measure OmegaMinus)
    (dampedDensityMinus dampedFrequencyMinus : OmegaMinus → ℂ)
    (boundaryDensityMinus : ℝ → ℂ)
    (zeroModePlus zeroModeMinus amplitude : ℂ)
    (hdampedDensityPlus : Integrable dampedDensityPlus muPlus)
    (hdampedFrequencyPlus : Measurable dampedFrequencyPlus)
    (hdampedPlus : ∀ᵐ x ∂muPlus, (dampedFrequencyPlus x).im < 0)
    (hboundaryPlus : Integrable boundaryDensityPlus)
    (hdampedDensityMinus : Integrable dampedDensityMinus muMinus)
    (hdampedFrequencyMinus : Measurable dampedFrequencyMinus)
    (hdampedMinus : ∀ᵐ x ∂muMinus, (dampedFrequencyMinus x).im < 0)
    (hboundaryMinus : Integrable boundaryDensityMinus)
    (absorbedMass : NNReal) (q : XiZeroCopy)
    (hplus : Tendsto
      (d4BMPassivePeripheralSpectralPhaseFullPoleNumerator
        muPlus dampedDensityPlus dampedFrequencyPlus boundaryDensityPlus
          zeroModePlus amplitude absorbedMass q)
      atTop (𝓝 0))
    (hminus : Tendsto
      (d4BMPassivePeripheralSpectralPhaseFullPoleNumerator
        muMinus dampedDensityMinus dampedFrequencyMinus boundaryDensityMinus
          zeroModeMinus (-amplitude) absorbedMass q)
      atTop (𝓝 0)) :
    zeroModeMinus - zeroModePlus =
      2 * d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) := by
  have hp := (d4BMPassivePeripheralSpectralPhaseFullPoleNumerator_tendsto_zero_iff_zeroMode
    muPlus dampedDensityPlus dampedFrequencyPlus boundaryDensityPlus zeroModePlus amplitude
    hdampedDensityPlus hdampedFrequencyPlus hdampedPlus hboundaryPlus absorbedMass q).mp hplus
  have hm := (d4BMPassivePeripheralSpectralPhaseFullPoleNumerator_tendsto_zero_iff_zeroMode
    muMinus dampedDensityMinus dampedFrequencyMinus boundaryDensityMinus zeroModeMinus (-amplitude)
    hdampedDensityMinus hdampedFrequencyMinus hdampedMinus hboundaryMinus absorbedMass q).mp hminus
  rw [d4FundamentalQNMCrossBranchAIMENumerator_neg] at hm
  rw [hm, hp]
  ring

/-- A phase-blind threshold atom cannot cancel both physical half-turn seed sectors. -/
theorem not_d4BMPassivePeripheralSpectralPhaseBlindThreshold_both_halfTurn_cancel
    {OmegaPlus OmegaMinus : Type*}
    [MeasurableSpace OmegaPlus] [MeasurableSpace OmegaMinus]
    (muPlus : Measure OmegaPlus)
    (dampedDensityPlus dampedFrequencyPlus : OmegaPlus → ℂ)
    (boundaryDensityPlus : ℝ → ℂ)
    (muMinus : Measure OmegaMinus)
    (dampedDensityMinus dampedFrequencyMinus : OmegaMinus → ℂ)
    (boundaryDensityMinus : ℝ → ℂ)
    (zeroMode amplitude : ℂ) (ha : amplitude ≠ 0)
    (hdampedDensityPlus : Integrable dampedDensityPlus muPlus)
    (hdampedFrequencyPlus : Measurable dampedFrequencyPlus)
    (hdampedPlus : ∀ᵐ x ∂muPlus, (dampedFrequencyPlus x).im < 0)
    (hboundaryPlus : Integrable boundaryDensityPlus)
    (hdampedDensityMinus : Integrable dampedDensityMinus muMinus)
    (hdampedFrequencyMinus : Measurable dampedFrequencyMinus)
    (hdampedMinus : ∀ᵐ x ∂muMinus, (dampedFrequencyMinus x).im < 0)
    (hboundaryMinus : Integrable boundaryDensityMinus)
    (absorbedMass : NNReal) (q : XiZeroCopy) :
    ¬ (Tendsto
        (d4BMPassivePeripheralSpectralPhaseFullPoleNumerator
          muPlus dampedDensityPlus dampedFrequencyPlus boundaryDensityPlus
            zeroMode amplitude absorbedMass q)
        atTop (𝓝 0) ∧
      Tendsto
        (d4BMPassivePeripheralSpectralPhaseFullPoleNumerator
          muMinus dampedDensityMinus dampedFrequencyMinus boundaryDensityMinus
            zeroMode (-amplitude) absorbedMass q)
        atTop (𝓝 0)) := by
  rintro ⟨hplus, hminus⟩
  have hjump := d4BMPassivePeripheralSpectral_halfTurnCancellation_forces_zeroModeJump
    muPlus dampedDensityPlus dampedFrequencyPlus boundaryDensityPlus
    muMinus dampedDensityMinus dampedFrequencyMinus boundaryDensityMinus
    zeroMode zeroMode amplitude hdampedDensityPlus hdampedFrequencyPlus hdampedPlus hboundaryPlus
    hdampedDensityMinus hdampedFrequencyMinus hdampedMinus hboundaryMinus absorbedMass q
    hplus hminus
  have hnum : d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) = 0 := by
    have htwo : (2 : ℂ) *
        d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) = 0 := by
      simpa using hjump.symm
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact ((d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude q).mpr ha) hnum

/-- Closed route class: two arbitrary regular peripheral transient spectra, one phase-blind
threshold atom, and one passive stationary term cannot extinguish both half-turn AIME sectors. -/
def D4BMPassivePeripheralSpectralPhaseBlindThresholdCancellationRouteKilled : Prop :=
  ∀ (OmegaPlus OmegaMinus : Type)
    [MeasurableSpace OmegaPlus] [MeasurableSpace OmegaMinus]
    (muPlus : Measure OmegaPlus)
    (dampedDensityPlus dampedFrequencyPlus : OmegaPlus → ℂ)
    (boundaryDensityPlus : ℝ → ℂ)
    (muMinus : Measure OmegaMinus)
    (dampedDensityMinus dampedFrequencyMinus : OmegaMinus → ℂ)
    (boundaryDensityMinus : ℝ → ℂ)
    (zeroMode amplitude : ℂ),
    amplitude ≠ 0 →
    Integrable dampedDensityPlus muPlus →
    Measurable dampedFrequencyPlus →
    (∀ᵐ x ∂muPlus, (dampedFrequencyPlus x).im < 0) →
    Integrable boundaryDensityPlus →
    Integrable dampedDensityMinus muMinus →
    Measurable dampedFrequencyMinus →
    (∀ᵐ x ∂muMinus, (dampedFrequencyMinus x).im < 0) →
    Integrable boundaryDensityMinus →
    ∀ (absorbedMass : NNReal) (q : XiZeroCopy),
      ¬ (Tendsto
          (d4BMPassivePeripheralSpectralPhaseFullPoleNumerator
            muPlus dampedDensityPlus dampedFrequencyPlus boundaryDensityPlus
              zeroMode amplitude absorbedMass q)
          atTop (𝓝 0) ∧
        Tendsto
          (d4BMPassivePeripheralSpectralPhaseFullPoleNumerator
            muMinus dampedDensityMinus dampedFrequencyMinus boundaryDensityMinus
              zeroMode (-amplitude) absorbedMass q)
          atTop (𝓝 0))

/-- Premise-free certificate killing source-independent phase-blind threshold completion in the
regular finite-variation HB peripheral spectral class. -/
theorem d4BMPassivePeripheralSpectralPhaseBlindThresholdCancellationRouteKilled :
    D4BMPassivePeripheralSpectralPhaseBlindThresholdCancellationRouteKilled := by
  intro OmegaPlus OmegaMinus _ _
    muPlus dampedDensityPlus dampedFrequencyPlus boundaryDensityPlus
    muMinus dampedDensityMinus dampedFrequencyMinus boundaryDensityMinus
    zeroMode amplitude ha
    hdampedDensityPlus hdampedFrequencyPlus hdampedPlus hboundaryPlus
    hdampedDensityMinus hdampedFrequencyMinus hdampedMinus hboundaryMinus
    absorbedMass q
  exact not_d4BMPassivePeripheralSpectralPhaseBlindThreshold_both_halfTurn_cancel
    muPlus dampedDensityPlus dampedFrequencyPlus boundaryDensityPlus
    muMinus dampedDensityMinus dampedFrequencyMinus boundaryDensityMinus
    zeroMode amplitude ha
    hdampedDensityPlus hdampedFrequencyPlus hdampedPlus hboundaryPlus
    hdampedDensityMinus hdampedFrequencyMinus hdampedMinus hboundaryMinus
    absorbedMass q

end

end RHTower
