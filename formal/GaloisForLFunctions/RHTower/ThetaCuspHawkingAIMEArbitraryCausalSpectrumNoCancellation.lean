import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskyDelayedPumpProbe
import GaloisForLFunctions.HTGeometry.ExpRayL2

/-!
# Arbitrary causal-spectrum exclusion for the HB AIME pole

The exact fundamental Birmingham--Mokhtari AIME numerator is nonzero on every Xi fibre. Earlier
work excluded its cancellation by finite local QNM packets and one uniformly damped continuum.
This module removes both restrictions.

Let an arbitrary measure space label a causal spectral completion. Its density may be complex and
the damping rates may accumulate at zero. If the density has finite variation (`L1`) and almost
every frequency remains strictly in the lower half-plane, then pointwise exponential damping and
one integrable majorant imply extinction of the entire response by dominated convergence. No
uniform damping gap and no QNM completeness statement is used.

Consequently no such infinite threshold spectrum can supply the unique persistent counterterm
that erases normalized AIME. Adding a passive stationary mass response only multiplies the
nonzero stationary numerator by a positive factor. The complete negative-branch fundamental pole
therefore eventually has exact order `-1`.

The sharp positive survivor is peripheral-spectrum rigidity: a persistent nonzero finite-variation
counterterm forces spectral mass outside the strictly damped sector. Hence any remaining HB
cancellation must use a zero-damping/growing mode or leave finite variation.

`[NEW] [HB] [AIME] [ARBITRARY SPECTRUM] [NO UNIFORM GAP] [POLE SURVIVAL] [LEAN-PROVED]`
-/

open Complex Real Set Filter Topology MeasureTheory

namespace RHTower

noncomputable section

/-- Arbitrary finite-variation causal spectral contribution to the full same-pole source. -/
def d4BMCausalSpectralSourceRemainder
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (density frequency : Omega -> ℂ) (delay : ℝ) : ℂ :=
  ∫ x, density x * Complex.exp
    (-(Complex.I * frequency x * (delay : ℂ))) ∂mu

private lemma d4BMDampedCharacter_tendsto_zero
    (omega : ℂ) (homega : omega.im < 0) :
    Tendsto (fun delay : ℝ =>
      Complex.exp (-(Complex.I * omega * (delay : ℂ))))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [Complex.norm_exp]
  have hre : ∀ delay : ℝ,
      (-(Complex.I * omega * (delay : ℂ))).re =
        -(-omega.im * delay) := by
    intro delay
    simp [Complex.mul_re]
  simp_rw [hre]
  exact GaloisForLFunctions.HTGeometry.tendsto_exp_neg_mul_atTop_nhds_zero
    (neg_pos.mpr homega)

/-- Every finite-variation superposition of strictly damped causal modes decays. Damping may
accumulate at zero and the spectral space may be arbitrary. -/
theorem d4BMCausalSpectralSourceRemainder_tendsto_zero
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (density frequency : Omega -> ℂ)
    (hdensity : Integrable density mu) (hfrequency : Measurable frequency)
    (hdamped : ∀ᵐ x ∂mu, (frequency x).im < 0) :
    Tendsto (d4BMCausalSpectralSourceRemainder mu density frequency)
      atTop (nhds 0) := by
  unfold d4BMCausalSpectralSourceRemainder
  rw [show (0 : ℂ) = ∫ _x : Omega, (0 : ℂ) ∂mu by simp]
  have hmeas : ∀ delay : ℝ,
      AEStronglyMeasurable
        (fun x => density x * Complex.exp
          (-(Complex.I * frequency x * (delay : ℂ)))) mu := by
    intro delay
    apply hdensity.aestronglyMeasurable.mul
    apply Measurable.aestronglyMeasurable
    apply Measurable.cexp
    exact (((measurable_const.mul hfrequency).mul measurable_const).neg)
  refine tendsto_integral_filter_of_dominated_convergence
    (F := fun (delay : ℝ) x => density x * Complex.exp
      (-(Complex.I * frequency x * (delay : ℂ))))
    (f := fun _ => (0 : ℂ)) (l := atTop)
    (fun x => ‖density x‖) ?_ ?_ hdensity.norm ?_
  · exact Filter.Eventually.of_forall hmeas
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with delay hdelay
    filter_upwards [hdamped] with x hx
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(Complex.I * frequency x * (delay : ℂ))).re =
        (frequency x).im * delay := by
      simp [Complex.mul_re]
    rw [hre]
    have hexp : Real.exp ((frequency x).im * delay) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr
        (mul_nonpos_of_nonpos_of_nonneg (le_of_lt hx) hdelay)
    exact mul_le_of_le_one_right (norm_nonneg _) hexp
  · filter_upwards [hdamped] with x hx
    simpa using
      (d4BMDampedCharacter_tendsto_zero (frequency x) hx).const_mul (density x)

/-- A persistent nonzero finite-variation response cannot be supported almost everywhere on
strictly damped frequencies. -/
theorem d4BMCausalSpectralPersistentCounterterm_forces_not_ae_strictlyDamped
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (density frequency : Omega -> ℂ)
    (hdensity : Integrable density mu) (hfrequency : Measurable frequency)
    {counterterm : ℂ} (hcounterterm : counterterm ≠ 0)
    (hpersistent : ∀ᶠ delay in atTop,
      d4BMCausalSpectralSourceRemainder mu density frequency delay = counterterm) :
    ¬ ∀ᵐ x ∂mu, (frequency x).im < 0 := by
  intro hdamped
  have hzero := d4BMCausalSpectralSourceRemainder_tendsto_zero
    mu density frequency hdensity hfrequency hdamped
  have hne : ∀ᶠ delay in atTop,
      d4BMCausalSpectralSourceRemainder mu density frequency delay ≠ counterterm :=
    hzero.eventually (eventually_ne_nhds hcounterterm.symm)
  rcases (hpersistent.and hne).exists with ⟨delay, heq, hne'⟩
  exact hne' heq

/-- Full normalized pole numerator with passive stationary mass and an arbitrary causal
finite-variation spectral completion. -/
def d4BMPassiveArbitraryCausalSpectralFullPoleNumerator
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (density frequency : Omega -> ℂ)
    (absorbedMass : NNReal) (q : XiZeroCopy) (delay : ℝ) : ℂ :=
  d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q) +
    d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q) +
    d4BMCausalSpectralSourceRemainder mu density frequency delay

/-- Arbitrary causal spectral completion decays to the nonzero passive AIME stationary
numerator. -/
theorem d4BMPassiveArbitraryCausalSpectralFullPoleNumerator_tendsto
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (density frequency : Omega -> ℂ)
    (hdensity : Integrable density mu) (hfrequency : Measurable frequency)
    (hdamped : ∀ᵐ x ∂mu, (frequency x).im < 0)
    (absorbedMass : NNReal) (q : XiZeroCopy) :
    Tendsto
      (d4BMPassiveArbitraryCausalSpectralFullPoleNumerator
        mu density frequency absorbedMass q)
      atTop
      (nhds (d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q) +
        d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q))) := by
  unfold d4BMPassiveArbitraryCausalSpectralFullPoleNumerator
  simpa using tendsto_const_nhds.add
    (d4BMCausalSpectralSourceRemainder_tendsto_zero
      mu density frequency hdensity hfrequency hdamped)

/-- No finite-variation superposition of strictly damped modes, even with damping accumulating at
zero, can erase normalized AIME plus passive stationary mass. -/
theorem eventually_d4BMPassiveArbitraryCausalSpectralFullPoleNumerator_ne_zero
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (density frequency : Omega -> ℂ)
    (hdensity : Integrable density mu) (hfrequency : Measurable frequency)
    (hdamped : ∀ᵐ x ∂mu, (frequency x).im < 0)
    (absorbedMass : NNReal) (q : XiZeroCopy) :
    ∀ᶠ delay in atTop,
      d4BMPassiveArbitraryCausalSpectralFullPoleNumerator
        mu density frequency absorbedMass q delay ≠ 0 := by
  have hlimit := d4BMPassiveArbitraryCausalSpectralFullPoleNumerator_tendsto
    mu density frequency hdensity hfrequency hdamped absorbedMass q
  exact hlimit.eventually
    (eventually_ne_nhds
      (d4BMPassiveStationaryFullNumerator_xi_ne_zero absorbedMass q))

/-- Sharp escape classification: persistent cancellation of normalized AIME plus passive mass by
a finite-variation spectral completion forces spectral mass outside the strictly damped sector. -/
theorem d4BMPassiveArbitraryCausalSpectral_forcedCounterterm
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (density frequency : Omega -> ℂ)
    (hdensity : Integrable density mu) (hfrequency : Measurable frequency)
    (absorbedMass : NNReal) (q : XiZeroCopy)
    (hpersistent : ∀ᶠ delay in atTop,
      d4BMCausalSpectralSourceRemainder mu density frequency delay =
        -(d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q) +
          d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q))) :
    ¬ ∀ᵐ x ∂mu, (frequency x).im < 0 := by
  apply d4BMCausalSpectralPersistentCounterterm_forces_not_ae_strictlyDamped
    mu density frequency hdensity hfrequency
  · exact neg_ne_zero.mpr
      (d4BMPassiveStationaryFullNumerator_xi_ne_zero absorbedMass q)
  · exact hpersistent

/-- Full cross-branch principal part with arbitrary causal spectral completion. -/
def d4BMPassiveArbitraryCausalSpectralPolePrincipalPart
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (density frequency : Omega -> ℂ)
    (absorbedMass : NNReal) (q : XiZeroCopy) (delay : ℝ) (omegaOut : ℂ) : ℂ :=
  d4FullCrossBranchPolePrincipalPart 1
    (fun _ => d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q) +
      d4BMCausalSpectralSourceRemainder mu density frequency delay)
    (xiSpectralPoint q) omegaOut

/-- HB capstone: every passive finite-variation strictly causal spectral completion eventually
retains the exact negative-branch fundamental BM simple pole. -/
theorem eventually_d4BMPassiveArbitraryCausalSpectralPole_order_qnmMinus_xi
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (density frequency : Omega -> ℂ)
    (hdensity : Integrable density mu) (hfrequency : Measurable frequency)
    (hdamped : ∀ᵐ x ∂mu, (frequency x).im < 0)
    (absorbedMass : NNReal) (q : XiZeroCopy) :
    ∀ᶠ delay in atTop,
      meromorphicOrderAt
        (d4BMPassiveArbitraryCausalSpectralPolePrincipalPart
          mu density frequency absorbedMass q delay)
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)) =
          ((-1 : ℤ) : WithTop ℤ) := by
  have hsurvive :=
    eventually_d4BMPassiveArbitraryCausalSpectralFullPoleNumerator_ne_zero
      mu density frequency hdensity hfrequency hdamped absorbedMass q
  filter_upwards [hsurvive] with delay hnonzero
  unfold d4BMPassiveArbitraryCausalSpectralPolePrincipalPart
  apply (d4FullCrossBranchPolePrincipalPart_order_qnmMinus_xi_iff
    1 (fun _ => d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q) +
      d4BMCausalSpectralSourceRemainder mu density frequency delay) q).2
  intro hcounterterm
  apply hnonzero
  unfold d4BMPassiveArbitraryCausalSpectralFullPoleNumerator
  rw [add_assoc, hcounterterm]
  ring

/-- Closed route-class statement: all finite-variation strictly damped causal completions retain
the fundamental BM pole after any passive stationary mass response. -/
def D4BMPassiveArbitraryCausalSpectralCancellationRouteKilled : Prop :=
  ∀ (Omega : Type) [MeasurableSpace Omega]
    (mu : Measure Omega) (density frequency : Omega -> ℂ),
    Integrable density mu ->
    Measurable frequency ->
    (∀ᵐ x ∂mu, (frequency x).im < 0) ->
    ∀ (absorbedMass : NNReal) (q : XiZeroCopy),
      ∀ᶠ delay in atTop,
        meromorphicOrderAt
          (d4BMPassiveArbitraryCausalSpectralPolePrincipalPart
            mu density frequency absorbedMass q delay)
          (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)) =
            ((-1 : ℤ) : WithTop ℤ)

/-- Premise-free Lean certificate killing the entire passive finite-variation strictly damped
spectral cancellation route. -/
theorem d4BMPassiveArbitraryCausalSpectralCancellationRouteKilled :
    D4BMPassiveArbitraryCausalSpectralCancellationRouteKilled := by
  intro Omega _ mu density frequency hdensity hfrequency hdamped absorbedMass q
  exact eventually_d4BMPassiveArbitraryCausalSpectralPole_order_qnmMinus_xi
    mu density frequency hdensity hfrequency hdamped absorbedMass q

end

end RHTower
