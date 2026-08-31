import GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEArbitraryCausalSpectrumNoCancellation
import GaloisForLFunctions.HTGeometry.AnnealedSpectralDephasing

/-!
# HB AIME peripheral-spectrum zero-mode rigidity

The preceding arbitrary-spectrum theorem shows that every finite-variation response supported
strictly in the lower frequency half-plane decays.  Current Schwarzschild Green-function theory
also leaves a real-axis threshold continuum (the branch cut) as a possible late-time counterterm.
This module closes that ordinary continuum escape.

Split the most general response treated here into

`zero mode + strictly damped finite-variation spectrum + L¹ real-axis continuum`.

Dominated convergence kills the damped term and Riemann--Lebesgue kills the absolutely continuous
boundary term.  The response therefore converges exactly to its zero-frequency atom.  Adding the
already-derived nonzero AIME numerator and passive stationary mass yields the sharp classification:
late-time cancellation occurs exactly when the zero atom is the negative stationary numerator.
Without such an atom, the fundamental negative-branch QNM retains exact meromorphic order `-1`.

This kills all ordinary finite-variation QNM/redshift plus `L¹` branch-cut completions as the
remaining HB producer.  The strongest survivor is equally exact: successful completion must use
the source-tuned zero-frequency atom, singular non-Rajchman peripheral spectrum, or infinite
variation.  No QNM completeness, positivity, KMS law, RH premise, or numerical input is used.

`[NEW] [HB] [AIME] [PERIPHERAL SPECTRUM] [ZERO-MODE RIGIDITY] [ROUTE KILL] [LEAN-PROVED]`
-/

open Complex Real Set Filter Topology MeasureTheory
open scoped FourierTransform

namespace RHTower

noncomputable section

/-- Absolutely continuous real-axis boundary-continuum return. -/
def d4BMACBoundaryContinuumSourceRemainder
    (density : ℝ → ℂ) (delay : ℝ) : ℂ :=
  ∫ frequency : ℝ,
    Complex.exp (-(Complex.I * (frequency : ℂ) * (delay : ℂ))) *
      density frequency

/-- Every `L¹` real-axis continuum dephases at late time. -/
theorem d4BMACBoundaryContinuumSourceRemainder_tendsto_zero
    (density : ℝ → ℂ) (_hdensity : Integrable density) :
    Tendsto (d4BMACBoundaryContinuumSourceRemainder density) atTop (𝓝 0) := by
  have hRL := Real.tendsto_integral_exp_smul_cocompact (f := density)
  have hscale : Tendsto (fun delay : ℝ => delay / (2 * Real.pi)) atTop atTop := by
    simp only [div_eq_mul_inv]
    exact tendsto_id.atTop_mul_const
      (show (0 : ℝ) < (2 * Real.pi)⁻¹ by positivity)
  have hco : Tendsto (fun delay : ℝ => delay / (2 * Real.pi)) atTop (cocompact ℝ) :=
    hscale.mono_right (le_trans le_sup_right
      (le_of_eq cocompact_eq_atBot_atTop.symm))
  have hcomp := hRL.comp hco
  refine hcomp.congr fun delay => ?_
  unfold d4BMACBoundaryContinuumSourceRemainder
  apply integral_congr_ae
  filter_upwards with frequency
  rw [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
  congr 2
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Most general finite-variation response covered here: one stationary zero mode, arbitrary
strictly damped finite-variation spectrum, and an `L¹` real-axis continuum. -/
def d4BMPeripheralSpectralSourceRemainder
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (dampedDensity dampedFrequency : Omega → ℂ)
    (boundaryDensity : ℝ → ℂ) (zeroMode : ℂ) (delay : ℝ) : ℂ :=
  zeroMode +
    d4BMCausalSpectralSourceRemainder mu dampedDensity dampedFrequency delay +
    d4BMACBoundaryContinuumSourceRemainder boundaryDensity delay

/-- The mixed peripheral response converges exactly to its zero-frequency atom. -/
theorem d4BMPeripheralSpectralSourceRemainder_tendsto_zeroMode
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (dampedDensity dampedFrequency : Omega → ℂ)
    (boundaryDensity : ℝ → ℂ) (zeroMode : ℂ)
    (hdampedDensity : Integrable dampedDensity mu)
    (hdampedFrequency : Measurable dampedFrequency)
    (hdamped : ∀ᵐ x ∂mu, (dampedFrequency x).im < 0)
    (hboundary : Integrable boundaryDensity) :
    Tendsto
      (d4BMPeripheralSpectralSourceRemainder
        mu dampedDensity dampedFrequency boundaryDensity zeroMode)
      atTop (𝓝 zeroMode) := by
  have hD := d4BMCausalSpectralSourceRemainder_tendsto_zero
    mu dampedDensity dampedFrequency hdampedDensity hdampedFrequency hdamped
  have hB := d4BMACBoundaryContinuumSourceRemainder_tendsto_zero
    boundaryDensity hboundary
  change Tendsto
    (fun delay => zeroMode +
      d4BMCausalSpectralSourceRemainder
        mu dampedDensity dampedFrequency delay +
      d4BMACBoundaryContinuumSourceRemainder boundaryDensity delay)
    atTop (𝓝 zeroMode)
  simpa only [add_zero] using (tendsto_const_nhds.add hD).add hB

/-- Sharp classification: a proposed late-time counterterm is exactly the zero-frequency atom. -/
theorem d4BMPeripheralSpectralSourceRemainder_tendsto_iff_zeroMode
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (dampedDensity dampedFrequency : Omega → ℂ)
    (boundaryDensity : ℝ → ℂ) (zeroMode counterterm : ℂ)
    (hdampedDensity : Integrable dampedDensity mu)
    (hdampedFrequency : Measurable dampedFrequency)
    (hdamped : ∀ᵐ x ∂mu, (dampedFrequency x).im < 0)
    (hboundary : Integrable boundaryDensity) :
    Tendsto
        (d4BMPeripheralSpectralSourceRemainder
          mu dampedDensity dampedFrequency boundaryDensity zeroMode)
        atTop (𝓝 counterterm) ↔
      zeroMode = counterterm := by
  have hzeroMode := d4BMPeripheralSpectralSourceRemainder_tendsto_zeroMode
    mu dampedDensity dampedFrequency boundaryDensity zeroMode
    hdampedDensity hdampedFrequency hdamped hboundary
  constructor
  · intro hcounterterm
    exact tendsto_nhds_unique hzeroMode hcounterterm
  · intro hzero
    simpa only [hzero] using hzeroMode

/-- Eventual exact cancellation also forces the same threshold atom. -/
theorem d4BMPeripheralSpectralPersistentCounterterm_eq_zeroMode
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (dampedDensity dampedFrequency : Omega → ℂ)
    (boundaryDensity : ℝ → ℂ) (zeroMode counterterm : ℂ)
    (hdampedDensity : Integrable dampedDensity mu)
    (hdampedFrequency : Measurable dampedFrequency)
    (hdamped : ∀ᵐ x ∂mu, (dampedFrequency x).im < 0)
    (hboundary : Integrable boundaryDensity)
    (hpersistent : ∀ᶠ delay in atTop,
      d4BMPeripheralSpectralSourceRemainder
        mu dampedDensity dampedFrequency boundaryDensity zeroMode delay = counterterm) :
    zeroMode = counterterm := by
  apply (d4BMPeripheralSpectralSourceRemainder_tendsto_iff_zeroMode
    mu dampedDensity dampedFrequency boundaryDensity zeroMode counterterm
    hdampedDensity hdampedFrequency hdamped hboundary).mp
  exact tendsto_const_nhds.congr'
    (hpersistent.mono fun _delay h => h.symm)

/-- Full AIME pole numerator with passive stationary mass and the mixed peripheral completion. -/
def d4BMPassivePeripheralSpectralFullPoleNumerator
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (dampedDensity dampedFrequency : Omega → ℂ)
    (boundaryDensity : ℝ → ℂ) (zeroMode : ℂ)
    (absorbedMass : NNReal) (q : XiZeroCopy) (delay : ℝ) : ℂ :=
  d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q) +
    d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q) +
    d4BMPeripheralSpectralSourceRemainder
      mu dampedDensity dampedFrequency boundaryDensity zeroMode delay

/-- Total pole numerator converges to stationary AIME plus the zero-mode coefficient. -/
theorem d4BMPassivePeripheralSpectralFullPoleNumerator_tendsto
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (dampedDensity dampedFrequency : Omega → ℂ)
    (boundaryDensity : ℝ → ℂ) (zeroMode : ℂ)
    (hdampedDensity : Integrable dampedDensity mu)
    (hdampedFrequency : Measurable dampedFrequency)
    (hdamped : ∀ᵐ x ∂mu, (dampedFrequency x).im < 0)
    (hboundary : Integrable boundaryDensity)
    (absorbedMass : NNReal) (q : XiZeroCopy) :
    Tendsto
      (d4BMPassivePeripheralSpectralFullPoleNumerator
        mu dampedDensity dampedFrequency boundaryDensity zeroMode absorbedMass q)
      atTop
      (𝓝 (d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q) +
        d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q) + zeroMode)) := by
  unfold d4BMPassivePeripheralSpectralFullPoleNumerator
  simpa using tendsto_const_nhds.add
    (d4BMPeripheralSpectralSourceRemainder_tendsto_zeroMode
      mu dampedDensity dampedFrequency boundaryDensity zeroMode
      hdampedDensity hdampedFrequency hdamped hboundary)

/-- Exact forced threshold coefficient for asymptotic cancellation of AIME plus passive mass. -/
theorem d4BMPassivePeripheralSpectralFullPoleNumerator_tendsto_zero_iff_zeroMode
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (dampedDensity dampedFrequency : Omega → ℂ)
    (boundaryDensity : ℝ → ℂ) (zeroMode : ℂ)
    (hdampedDensity : Integrable dampedDensity mu)
    (hdampedFrequency : Measurable dampedFrequency)
    (hdamped : ∀ᵐ x ∂mu, (dampedFrequency x).im < 0)
    (hboundary : Integrable boundaryDensity)
    (absorbedMass : NNReal) (q : XiZeroCopy) :
    Tendsto
        (d4BMPassivePeripheralSpectralFullPoleNumerator
          mu dampedDensity dampedFrequency boundaryDensity zeroMode absorbedMass q)
        atTop (𝓝 0) ↔
      zeroMode =
        -(d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q) +
          d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q)) := by
  have hlimit := d4BMPassivePeripheralSpectralFullPoleNumerator_tendsto
    mu dampedDensity dampedFrequency boundaryDensity zeroMode
    hdampedDensity hdampedFrequency hdamped hboundary absorbedMass q
  constructor
  · intro hzero
    have heq := tendsto_nhds_unique hlimit hzero
    exact eq_neg_of_add_eq_zero_right heq
  · intro hzeroMode
    convert hlimit using 1
    rw [hzeroMode]
    ring

/-- Without a zero mode, the completed pole numerator is eventually nonzero. -/
theorem eventually_d4BMPassivePeripheralSpectralFullPoleNumerator_ne_zero
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (dampedDensity dampedFrequency : Omega → ℂ)
    (boundaryDensity : ℝ → ℂ)
    (hdampedDensity : Integrable dampedDensity mu)
    (hdampedFrequency : Measurable dampedFrequency)
    (hdamped : ∀ᵐ x ∂mu, (dampedFrequency x).im < 0)
    (hboundary : Integrable boundaryDensity)
    (absorbedMass : NNReal) (q : XiZeroCopy) :
    ∀ᶠ delay in atTop,
      d4BMPassivePeripheralSpectralFullPoleNumerator
        mu dampedDensity dampedFrequency boundaryDensity 0 absorbedMass q delay ≠ 0 := by
  have hlimit := d4BMPassivePeripheralSpectralFullPoleNumerator_tendsto
    mu dampedDensity dampedFrequency boundaryDensity 0
    hdampedDensity hdampedFrequency hdamped hboundary absorbedMass q
  have hlimit' : Tendsto
      (d4BMPassivePeripheralSpectralFullPoleNumerator
        mu dampedDensity dampedFrequency boundaryDensity 0 absorbedMass q)
      atTop
      (𝓝 (d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q) +
        d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q))) := by
    simpa only [add_zero] using hlimit
  exact hlimit'.eventually
    (eventually_ne_nhds
      (d4BMPassiveStationaryFullNumerator_xi_ne_zero absorbedMass q))

/-- Principal part of the completed negative-branch fundamental pole. -/
def d4BMPassivePeripheralSpectralPolePrincipalPart
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (dampedDensity dampedFrequency : Omega → ℂ)
    (boundaryDensity : ℝ → ℂ) (zeroMode : ℂ)
    (absorbedMass : NNReal) (q : XiZeroCopy) (delay : ℝ) (omegaOut : ℂ) : ℂ :=
  d4FullCrossBranchPolePrincipalPart 1
    (fun _ => d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q) +
      d4BMPeripheralSpectralSourceRemainder
        mu dampedDensity dampedFrequency boundaryDensity zeroMode delay)
    (xiSpectralPoint q) omegaOut

/-- Every no-zero-mode mixed peripheral completion eventually retains the exact simple pole. -/
theorem eventually_d4BMPassivePeripheralSpectralPole_order_qnmMinus_xi
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (dampedDensity dampedFrequency : Omega → ℂ)
    (boundaryDensity : ℝ → ℂ)
    (hdampedDensity : Integrable dampedDensity mu)
    (hdampedFrequency : Measurable dampedFrequency)
    (hdamped : ∀ᵐ x ∂mu, (dampedFrequency x).im < 0)
    (hboundary : Integrable boundaryDensity)
    (absorbedMass : NNReal) (q : XiZeroCopy) :
    ∀ᶠ delay in atTop,
      meromorphicOrderAt
        (d4BMPassivePeripheralSpectralPolePrincipalPart
          mu dampedDensity dampedFrequency boundaryDensity 0 absorbedMass q delay)
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)) =
          ((-1 : ℤ) : WithTop ℤ) := by
  have hsurvive := eventually_d4BMPassivePeripheralSpectralFullPoleNumerator_ne_zero
    mu dampedDensity dampedFrequency boundaryDensity
    hdampedDensity hdampedFrequency hdamped hboundary absorbedMass q
  filter_upwards [hsurvive] with delay hnonzero
  unfold d4BMPassivePeripheralSpectralPolePrincipalPart
  apply (d4FullCrossBranchPolePrincipalPart_order_qnmMinus_xi_iff
    1 (fun _ => d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q) +
      d4BMPeripheralSpectralSourceRemainder
        mu dampedDensity dampedFrequency boundaryDensity 0 delay) q).2
  intro hcounterterm
  apply hnonzero
  unfold d4BMPassivePeripheralSpectralFullPoleNumerator
  rw [add_assoc, hcounterterm]
  ring

/-- Route class: finite-variation LHP modes plus an `L¹` real-axis continuum, with no threshold
atom, cannot cancel the AIME pole after passive stationary backreaction. -/
def D4BMPassivePeripheralSpectralNoZeroModeCancellationRouteKilled : Prop :=
  ∀ (Omega : Type) [MeasurableSpace Omega]
    (mu : Measure Omega) (dampedDensity dampedFrequency : Omega → ℂ)
    (boundaryDensity : ℝ → ℂ),
    Integrable dampedDensity mu →
    Measurable dampedFrequency →
    (∀ᵐ x ∂mu, (dampedFrequency x).im < 0) →
    Integrable boundaryDensity →
    ∀ (absorbedMass : NNReal) (q : XiZeroCopy),
      ∀ᶠ delay in atTop,
        meromorphicOrderAt
          (d4BMPassivePeripheralSpectralPolePrincipalPart
            mu dampedDensity dampedFrequency boundaryDensity 0 absorbedMass q delay)
          (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)) =
            ((-1 : ℤ) : WithTop ℤ)

/-- Premise-free certificate killing the ordinary no-zero-mode peripheral completion route. -/
theorem d4BMPassivePeripheralSpectralNoZeroModeCancellationRouteKilled :
    D4BMPassivePeripheralSpectralNoZeroModeCancellationRouteKilled := by
  intro Omega _ mu dampedDensity dampedFrequency boundaryDensity
    hdampedDensity hdampedFrequency hdamped hboundary absorbedMass q
  exact eventually_d4BMPassivePeripheralSpectralPole_order_qnmMinus_xi
    mu dampedDensity dampedFrequency boundaryDensity
    hdampedDensity hdampedFrequency hdamped hboundary absorbedMass q

end

end RHTower

