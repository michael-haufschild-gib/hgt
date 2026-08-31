import GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEPhaseBlindThresholdSpectrumNoGo

/-!
# HB regular peripheral threshold: complete cancellation classification

For the full regular peripheral class—strictly damped finite-variation modes, an `L¹`
real-axis continuum, one zero-frequency atom, and passive stationary mass—this file closes both
possible threshold strategies.

The transient spectrum vanishes at late time, so cancellation occurs exactly when the threshold
atom is the canonical negative of AIME plus passive mass.  That atom always cancels and is unique,
making source-adapted existence target-fitted rather than selective.  Cubic half-turn covariance
forces the two canonical phase atoms to differ by exactly twice the nonzero AIME numerator, so one
source-independent phase-blind atom cannot cancel both sectors.

Thus no regular peripheral threshold response supplies the missing HB producer.  A survivor must
derive the canonical odd zero-mode jump independently from the physical source law, or leave this
class through singular non-Rajchman/infinite-variation or domain-sensitive dynamics.

`[NEW] [HB] [AIME] [THRESHOLD] [COMPLETE CLASSIFICATION] [ROUTE KILL] [LEAN-PROVED]`
-/

open Complex Real Set Filter Topology MeasureTheory

namespace RHTower

noncomputable section

/-- Unique threshold atom that cancels the regular peripheral AIME completion. -/
def d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode
    (amplitude : ℂ) (absorbedMass : NNReal) (q : XiZeroCopy) : ℂ :=
  -(d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) +
    d4BMPassiveStationaryMassNumerator absorbedMass (xiSpectralPoint q))

/-- A regular peripheral completion cancels exactly at the canonical phase-adapted atom. -/
theorem d4BMPassivePeripheralSpectralPhaseCancellation_iff_eq_canonicalZeroMode
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
        d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode amplitude absorbedMass q := by
  simpa [d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode] using
    (d4BMPassivePeripheralSpectralPhaseFullPoleNumerator_tendsto_zero_iff_zeroMode
      mu dampedDensity dampedFrequency boundaryDensity zeroMode amplitude
      hdampedDensity hdampedFrequency hdamped hboundary absorbedMass q)

/-- The canonical phase-adapted atom cancels for every admissible regular transient spectrum. -/
theorem d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode_tendsto_zero
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (dampedDensity dampedFrequency : Omega → ℂ)
    (boundaryDensity : ℝ → ℂ) (amplitude : ℂ)
    (hdampedDensity : Integrable dampedDensity mu)
    (hdampedFrequency : Measurable dampedFrequency)
    (hdamped : ∀ᵐ x ∂mu, (dampedFrequency x).im < 0)
    (hboundary : Integrable boundaryDensity)
    (absorbedMass : NNReal) (q : XiZeroCopy) :
    Tendsto
      (d4BMPassivePeripheralSpectralPhaseFullPoleNumerator
        mu dampedDensity dampedFrequency boundaryDensity
          (d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode amplitude absorbedMass q)
          amplitude absorbedMass q)
      atTop (𝓝 0) := by
  exact (d4BMPassivePeripheralSpectralPhaseCancellation_iff_eq_canonicalZeroMode
    mu dampedDensity dampedFrequency boundaryDensity
    (d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode amplitude absorbedMass q) amplitude
    hdampedDensity hdampedFrequency hdamped hboundary absorbedMass q).2 rfl

/-- Opposite seed phases force the exact odd cubic jump between canonical threshold atoms. -/
theorem d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode_halfTurn_sub
    (amplitude : ℂ) (absorbedMass : NNReal) (q : XiZeroCopy) :
    d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode (-amplitude) absorbedMass q -
        d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode amplitude absorbedMass q =
      2 * d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) := by
  rw [d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode,
    d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode,
    d4FundamentalQNMCrossBranchAIMENumerator_neg]
  ring

/-- For a nonzero seed, the canonical threshold atom cannot be phase blind. -/
theorem d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode_halfTurn_ne
    (amplitude : ℂ) (absorbedMass : NNReal) (q : XiZeroCopy) (ha : amplitude ≠ 0) :
    d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode (-amplitude) absorbedMass q ≠
      d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode amplitude absorbedMass q := by
  intro hsame
  have hjump := d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode_halfTurn_sub
    amplitude absorbedMass q
  rw [hsame, sub_self] at hjump
  have hnum :
      d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) = 0 := by
    have htwo : (2 : ℂ) *
        d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) = 0 := by
      simpa using hjump.symm
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact ((d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude q).mpr ha) hnum

/-- Uniform existence-and-uniqueness classification for phase-adapted threshold cancellation. -/
def D4BMPassivePeripheralSpectralPhaseAdaptedThresholdCancellationClassified : Prop :=
  ∀ (Omega : Type) [MeasurableSpace Omega]
    (mu : Measure Omega)
    (dampedDensity dampedFrequency : Omega → ℂ)
    (boundaryDensity : ℝ → ℂ),
    Integrable dampedDensity mu →
    Measurable dampedFrequency →
    (∀ᵐ x ∂mu, (dampedFrequency x).im < 0) →
    Integrable boundaryDensity →
    ∀ (zeroMode amplitude : ℂ) (absorbedMass : NNReal) (q : XiZeroCopy),
      Tendsto
          (d4BMPassivePeripheralSpectralPhaseFullPoleNumerator
            mu dampedDensity dampedFrequency boundaryDensity
              zeroMode amplitude absorbedMass q)
          atTop (𝓝 0) ↔
        zeroMode =
          d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode amplitude absorbedMass q

/-- The regular threshold class is complete: source-blind cancellation is impossible, whereas
source-adapted cancellation is uniquely target-fitted and carries the exact cubic phase jump. -/
def D4BMPassiveRegularPeripheralThresholdCancellationRouteKilled : Prop :=
  D4BMPassivePeripheralSpectralPhaseBlindThresholdCancellationRouteKilled ∧
  D4BMPassivePeripheralSpectralPhaseAdaptedThresholdCancellationClassified ∧
  ∀ (amplitude : ℂ) (absorbedMass : NNReal) (q : XiZeroCopy),
    d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode (-amplitude) absorbedMass q -
        d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode amplitude absorbedMass q =
      2 * d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) ∧
    (amplitude ≠ 0 →
      d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode (-amplitude) absorbedMass q ≠
        d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode amplitude absorbedMass q)

/-- Premise-free certificate closing the complete regular peripheral threshold-response class. -/
theorem d4BMPassiveRegularPeripheralThresholdCancellationRouteKilled :
    D4BMPassiveRegularPeripheralThresholdCancellationRouteKilled := by
  refine ⟨d4BMPassivePeripheralSpectralPhaseBlindThresholdCancellationRouteKilled, ?_, ?_⟩
  · intro Omega _ mu dampedDensity dampedFrequency boundaryDensity
      hdampedDensity hdampedFrequency hdamped hboundary
      zeroMode amplitude absorbedMass q
    exact d4BMPassivePeripheralSpectralPhaseCancellation_iff_eq_canonicalZeroMode
      mu dampedDensity dampedFrequency boundaryDensity zeroMode amplitude
      hdampedDensity hdampedFrequency hdamped hboundary absorbedMass q
  · intro amplitude absorbedMass q
    exact ⟨d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode_halfTurn_sub
      amplitude absorbedMass q,
      d4BMPassivePeripheralSpectralCanonicalPhaseZeroMode_halfTurn_ne
        amplitude absorbedMass q⟩

end

end RHTower
