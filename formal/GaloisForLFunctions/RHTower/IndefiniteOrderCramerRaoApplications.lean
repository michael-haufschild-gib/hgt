import GaloisForLFunctions.QuantumAlg.Util.QuantumCramerRao
import GaloisForLFunctions.HTGeometry.BalancedQuantumSwitch
import GaloisForLFunctions.HTGeometry.FiniteInvolutiveClockQuantumFisherDephasing
import GaloisForLFunctions.HTGeometry.NormalizedMomentQuantumVariance
import GaloisForLFunctions.HTGeometry.PrimeBooleanFusionSourcePacket
import GaloisForLFunctions.HTGeometry.PrimeBooleanMassHankelQuantumFusion
import GaloisForLFunctions.RHTower.SoninLogClockQuantumFisher
import GaloisForLFunctions.RHTower.SoninCoupledProjectiveFeshbachEquivalence
import GaloisForLFunctions.RHTower.MixedStateQutritRecurrenceSeparation
import GaloisForLFunctions.RHTower.MixedStateQuquartMomentRecurrenceSeparation
import GaloisForLFunctions.RHTower.FiniteJetRecurrenceSeparation
import GaloisForLFunctions.RHTower.FermiMellinPhaseProperness
import GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZSchwarzschildNonMarkovEdge

/-!
# Indefinite-order and Cramer--Rao applications across the corpus

The balanced odd quantum-switch branch is half the commutator.  Existing corpus QFI
identities therefore become exact branch-intensity laws.  Existing scalar Fisher
identities also acquire extended SLD error statements, including singular models where
zero information means infinite error.
-/

open scoped InnerProductSpace

namespace HTGeometry

noncomputable section

open ConstraintFrameRelativity

/-- Closed nondegenerate moment data to which the corpus moment-QFI identity applies. -/
structure NondegenerateMomentCramerRaoModel where
  moments : ℕ → ℝ
  observable : Polynomial ℝ
  vacuumNonzero : moments 0 ≠ 0

/-- Every nondegenerate corpus moment model has SLD error reciprocal to four times normalized
variance. -/
theorem NondegenerateMomentCramerRaoModel.extendedSLDCRB_eq_normalizedVariance
    (model : NondegenerateMomentCramerRaoModel) :
    QuantumAlg.extendedScalarSLDCramerRao
        (pureStateQuantumFisherValue (model.moments 0)
          (momentFunctional model.moments model.observable)
          (momentFunctional model.moments (model.observable ^ 2))) =
      QuantumAlg.extendedScalarSLDCramerRao
        (4 * momentNormalizedVariance model.moments model.observable) := by
  rw [pureStateQuantumFisherValue_moment_eq_four_mul_normalizedVariance
    model.moments model.vacuumNonzero model.observable]

/-- Boolean parity-clock directional QFI transported to extended SLD error. -/
theorem booleanParityClock_extendedSLDCRB_eq_directional
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q lam : ι → ℝ) (t : ℝ) :
    QuantumAlg.extendedScalarSLDCramerRao
        (pureStateQuantumFisherValue 1
          (bernoulliExp q (linearStat fun p => Real.pi - t * lam p))
          (bernoulliExp q
            (fun S => (linearStat (fun p => Real.pi - t * lam p) S) ^ 2))) =
      QuantumAlg.extendedScalarSLDCramerRao
        (fusionDirectionalQFI (bernoulliVar q) lam t) := by
  rw [pureStateQuantumFisherValue_booleanParityClock_eq_directional]

/-- Full two-coordinate Boolean parity-clock tangent transported to extended SLD error. -/
theorem booleanParityClock_tangent_extendedSLDCRB_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q lam : ι → ℝ) (a b : ℝ) :
    QuantumAlg.extendedScalarSLDCramerRao
        (pureStateQuantumFisherValue 1
          (bernoulliExp q (linearStat fun p => Real.pi * a - b * lam p))
          (bernoulliExp q
            (fun S => (linearStat (fun p => Real.pi * a - b * lam p) S) ^ 2))) =
      QuantumAlg.extendedScalarSLDCramerRao
        (fusionTangentQFI (bernoulliVar q) lam a b) := by
  rw [pureStateQuantumFisherValue_parityClock_tangent]

/-- Closed data for an identifiable finite involutive-clock experiment. -/
structure FiniteInvolutiveSwitchMetrologyModel (K E : Type*) [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] [CompleteSpace E] where
  clock : E →L[K] E
  observable : E →L[K] E
  probe : E
  clock_isometry : clock.adjoint * clock = 1
  clock_involution : clock ^ 2 = 1
  probe_normalized : ‖probe‖ = 1
  probe_fixed : clock probe = probe

/-- Finite involutive-clock QFI is four times balanced odd-switch intensity. -/
theorem FiniteInvolutiveSwitchMetrologyModel.qfi_eq_four_mul_oddSwitchIntensity
    {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] [CompleteSpace E]
    (model : FiniteInvolutiveSwitchMetrologyModel K E) :
    pureStateQuantumFisherValue (‖model.probe‖ ^ 2)
        (‖inner K model.probe
          ((1 - finiteCyclicGaugeAverage model.clock 2)
            (model.observable model.probe))‖)
        (‖(1 - finiteCyclicGaugeAverage model.clock 2)
            (model.observable model.probe)‖ ^ 2) =
      4 * ‖balancedQuantumSwitchOdd model.observable model.clock model.probe‖ ^ 2 := by
  rw [finiteInvolutiveClock_erasedPureStateQuantumFisherValue_eq_commutatorNormSq
    model.clock model.observable model.clock_isometry model.clock_involution
    model.probe_normalized model.probe_fixed]
  exact norm_commutator_apply_sq_eq_four_mul_norm_balancedQuantumSwitchOdd_sq
    model.observable model.clock model.probe

/-- Corresponding extended SLD error is reciprocal odd-branch intensity. -/
theorem FiniteInvolutiveSwitchMetrologyModel.extendedSLDCRB_eq_oddSwitchIntensity
    {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] [CompleteSpace E]
    (model : FiniteInvolutiveSwitchMetrologyModel K E) :
    QuantumAlg.extendedScalarSLDCramerRao
        (pureStateQuantumFisherValue (‖model.probe‖ ^ 2)
          (‖inner K model.probe
            ((1 - finiteCyclicGaugeAverage model.clock 2)
              (model.observable model.probe))‖)
          (‖(1 - finiteCyclicGaugeAverage model.clock 2)
              (model.observable model.probe)‖ ^ 2)) =
      QuantumAlg.extendedScalarSLDCramerRao
        (4 * ‖balancedQuantumSwitchOdd model.observable model.clock model.probe‖ ^ 2) := by
  rw [model.qfi_eq_four_mul_oddSwitchIntensity]

/-- Infinite erased-clock estimation error is exactly a dark odd switch port. -/
theorem FiniteInvolutiveSwitchMetrologyModel.extendedSLDCRB_eq_top_iff_oddSwitchDark
    {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] [CompleteSpace E]
    (model : FiniteInvolutiveSwitchMetrologyModel K E) :
    QuantumAlg.extendedScalarSLDCramerRao
        (pureStateQuantumFisherValue (‖model.probe‖ ^ 2)
          (‖inner K model.probe
            ((1 - finiteCyclicGaugeAverage model.clock 2)
              (model.observable model.probe))‖)
          (‖(1 - finiteCyclicGaugeAverage model.clock 2)
              (model.observable model.probe)‖ ^ 2)) = ⊤ ↔
      balancedQuantumSwitchOdd model.observable model.clock model.probe = 0 := by
  rw [model.qfi_eq_four_mul_oddSwitchIntensity,
    QuantumAlg.extendedScalarSLDCramerRao_eq_top_iff]
  constructor
  · intro h
    have hnorm :
        ‖balancedQuantumSwitchOdd model.observable model.clock model.probe‖ = 0 := by
      nlinarith [norm_nonneg
        (balancedQuantumSwitchOdd model.observable model.clock model.probe)]
    exact norm_eq_zero.mp hnorm
  · rintro h
    simp [h]

end

end HTGeometry

namespace RHTower

noncomputable section

/-- Coupled all-prime Sonin QFI transported to its extended SLD-error variance law. -/
theorem soninAllPrimeCoupled_extendedSLDCRB_eq_normalizedVariance
    (a : SoninCoupledNondegenerateAperture) (p : Polynomial ℝ) :
    QuantumAlg.extendedScalarSLDCramerRao
        (soninAllPrimeCoupledPureStateQuantumFisherValue a.1 p) =
      QuantumAlg.extendedScalarSLDCramerRao
        (4 * HTGeometry.momentNormalizedVariance
          (soninAllPrimeCoupledRealTraceMoment a.1) p) := by
  rw [soninAllPrimeCoupledPureStateQuantumFisherValue_eq_four_mul_normalizedVariance]

/-- Closed Sonin data for the balanced switch between scattering and an observable. -/
structure SoninBalancedSwitchMetrologyModel where
  observable : SoninL2 →L[ℂ] SoninL2
  probe : SoninL2
  probe_normalized : ‖probe‖ = 1
  probe_physical : GaloisForLFunctions.PhysicalState
    (soninLogFourierScattering - 1).toLinearMap probe

/-- Sonin logarithmic-clock QFI is exactly four times balanced odd ICO intensity. -/
theorem SoninBalancedSwitchMetrologyModel.qfi_eq_four_mul_oddSwitchIntensity
    (model : SoninBalancedSwitchMetrologyModel) :
    HTGeometry.pureStateQuantumFisherValue (‖model.probe‖ ^ 2)
        (‖inner ℂ model.probe
          ((1 - soninLogFourierInvariantAverage) (model.observable model.probe))‖)
        (‖(1 - soninLogFourierInvariantAverage) (model.observable model.probe)‖ ^ 2) =
      4 * ‖HTGeometry.balancedQuantumSwitchOdd model.observable
        soninLogFourierScattering model.probe‖ ^ 2 := by
  rw [soninLogClock_erasedPureStateQuantumFisherValue_eq_commutatorNormSq
    model.observable model.probe_normalized model.probe_physical]
  exact HTGeometry.norm_commutator_apply_sq_eq_four_mul_norm_balancedQuantumSwitchOdd_sq
    model.observable soninLogFourierScattering model.probe

/-- Sonin extended SLD error is completely determined by odd ICO intensity. -/
theorem SoninBalancedSwitchMetrologyModel.extendedSLDCRB_eq_oddSwitchIntensity
    (model : SoninBalancedSwitchMetrologyModel) :
    QuantumAlg.extendedScalarSLDCramerRao
        (HTGeometry.pureStateQuantumFisherValue (‖model.probe‖ ^ 2)
          (‖inner ℂ model.probe
            ((1 - soninLogFourierInvariantAverage) (model.observable model.probe))‖)
          (‖(1 - soninLogFourierInvariantAverage) (model.observable model.probe)‖ ^ 2)) =
      QuantumAlg.extendedScalarSLDCramerRao
        (4 * ‖HTGeometry.balancedQuantumSwitchOdd model.observable
          soninLogFourierScattering model.probe‖ ^ 2) := by
  rw [model.qfi_eq_four_mul_oddSwitchIntensity]

/-- For the Sonin clock, infinite SLD error is exactly darkness of the odd ICO branch. -/
theorem SoninBalancedSwitchMetrologyModel.extendedSLDCRB_eq_top_iff_oddSwitchDark
    (model : SoninBalancedSwitchMetrologyModel) :
    QuantumAlg.extendedScalarSLDCramerRao
        (HTGeometry.pureStateQuantumFisherValue (‖model.probe‖ ^ 2)
          (‖inner ℂ model.probe
            ((1 - soninLogFourierInvariantAverage) (model.observable model.probe))‖)
          (‖(1 - soninLogFourierInvariantAverage) (model.observable model.probe)‖ ^ 2)) = ⊤ ↔
      HTGeometry.balancedQuantumSwitchOdd model.observable
        soninLogFourierScattering model.probe = 0 := by
  rw [model.qfi_eq_four_mul_oddSwitchIntensity,
    QuantumAlg.extendedScalarSLDCramerRao_eq_top_iff]
  constructor
  · intro h
    have hnorm :
        ‖HTGeometry.balancedQuantumSwitchOdd model.observable
          soninLogFourierScattering model.probe‖ = 0 := by
      nlinarith [norm_nonneg
        (HTGeometry.balancedQuantumSwitchOdd model.observable
          soninLogFourierScattering model.probe)]
    exact norm_eq_zero.mp hnorm
  · rintro h
    simp [h]

/-- The two explicit qutrit recurrence clocks have identical extended SLD error. -/
theorem qutrit_realized_extendedSLDCRB_eq :
    QuantumAlg.extendedScalarSLDCramerRao
        (mixedSpikeSLDQuantumFisher (1 / 6) (1 / 2)
          (finiteDiagonalHamiltonian qutritEnergy)
          (finiteWeightKet qutritPeriodicWeight)) =
      QuantumAlg.extendedScalarSLDCramerRao
        (mixedSpikeSLDQuantumFisher (1 / 6) (1 / 2)
          (finiteDiagonalHamiltonian qutritEnergy)
          (finiteWeightKet qutritAperiodicWeight)) := by
  rw [qutrit_realized_mixedSpikeSLDQuantumFisher_eq]

/-- Concrete qutrit QFI as a strictly positive scalar metrology model. -/
def qutritPositiveScalarQFI : QuantumAlg.PositiveScalarQFI where
  value := qutritMixedSpikeQuantumFisher qutritPeriodicWeight
  positive := qutrit_common_quantumFisher_pos

theorem qutritPositiveScalarQFI_sldCramerRao :
    qutritPositiveScalarQFI.sldCramerRao =
      (qutritMixedSpikeQuantumFisher qutritPeriodicWeight)⁻¹ := rfl

/-- Concrete qutrit clock has finite extended SLD error. -/
theorem qutritPositiveScalarQFI_extendedSLDCRB_ne_top :
    QuantumAlg.extendedScalarSLDCramerRao qutritPositiveScalarQFI.value ≠ ⊤ := by
  intro htop
  exact (not_le_of_gt qutritPositiveScalarQFI.positive)
    ((QuantumAlg.extendedScalarSLDCramerRao_eq_top_iff _).mp htop)

/-- The two explicit four-level recurrence clocks have identical extended SLD error. -/
theorem ququart_realized_extendedSLDCRB_eq :
    QuantumAlg.extendedScalarSLDCramerRao
        (mixedSpikeSLDQuantumFisher (1 / 8) (1 / 2)
          (finiteDiagonalHamiltonian ququartEnergy)
          (finiteWeightKet ququartPeriodicWeight)) =
      QuantumAlg.extendedScalarSLDCramerRao
        (mixedSpikeSLDQuantumFisher (1 / 8) (1 / 2)
          (finiteDiagonalHamiltonian ququartEnergy)
          (finiteWeightKet ququartAperiodicWeight)) := by
  rw [ququart_realized_mixedSpikeSLDQuantumFisher_eq]

/-- Dimension bundled with the exact nontriviality condition for finite jet clocks. -/
abbrev NontrivialFiniteClockDimension := {N : ℕ // 2 ≤ N}

/-- Periodic and aperiodic finite clocks have identical extended SLD time error. -/
theorem finiteClock_periodic_aperiodic_extendedSLDCRB_eq
    (N : NontrivialFiniteClockDimension) :
    QuantumAlg.extendedScalarSLDCramerRao
        (mixedSpikeSLDQuantumFisher 0 1
          (FiniteJet.clockHamiltonian N) (FiniteJet.periodicClock N)) =
      QuantumAlg.extendedScalarSLDCramerRao
        (mixedSpikeSLDQuantumFisher 0 1
          (FiniteJet.clockHamiltonian N) (FiniteJet.aperiodicClock N)) := by
  rw [FiniteJet.clock_quantumFisher_eq N N.property]

/-- Positive Mellin parameter bundled into closed metrology data. -/
abbrev PositiveMellinParameter := {sigma : ℝ // 0 < sigma}

/-- Fermi--Mellin SLD error is reciprocal to four times logarithmic variance. -/
theorem fermiMellin_extendedSLDCRB_eq_variance
    (sigma : PositiveMellinParameter) :
    QuantumAlg.extendedScalarSLDCramerRao
        (HTGeometry.pureStateQuantumFisherValue (fermiLogMoment sigma 0)
          (HTGeometry.momentFunctional (fermiLogMoment sigma) Polynomial.X)
          (HTGeometry.momentFunctional (fermiLogMoment sigma) (Polynomial.X ^ 2))) =
      QuantumAlg.extendedScalarSLDCramerRao (4 * fermiLogVariance sigma) := by
  rw [pureStateQuantumFisher_fermiMellin sigma.property]

/-- Positive Fermi logarithmic variance makes every bundled Mellin SLD error finite. -/
theorem fermiMellin_extendedSLDCRB_ne_top
    (sigma : PositiveMellinParameter) :
    QuantumAlg.extendedScalarSLDCramerRao
        (HTGeometry.pureStateQuantumFisherValue (fermiLogMoment sigma 0)
          (HTGeometry.momentFunctional (fermiLogMoment sigma) Polynomial.X)
          (HTGeometry.momentFunctional (fermiLogMoment sigma) (Polynomial.X ^ 2))) ≠ ⊤ := by
  intro htop
  have hpos : 0 < HTGeometry.pureStateQuantumFisherValue (fermiLogMoment sigma 0)
      (HTGeometry.momentFunctional (fermiLogMoment sigma) Polynomial.X)
      (HTGeometry.momentFunctional (fermiLogMoment sigma) (Polynomial.X ^ 2)) := by
    rw [pureStateQuantumFisher_fermiMellin sigma.property]
    exact mul_pos (by norm_num) (fermiLogVariance_pos sigma.property)
  exact (not_le_of_gt hpos)
    ((QuantumAlg.extendedScalarSLDCramerRao_eq_top_iff _).mp htop)

/-- Hawking far-zone spectral SLD error is reciprocal to four times Bose susceptibility. -/
theorem blackHoleFarZone_extendedSLDCRB_eq_susceptibility (base : ℕ) :
    QuantumAlg.extendedScalarSLDCramerRao
        (blackHoleFarZoneBoseSpectralQuantumFisher base) =
      QuantumAlg.extendedScalarSLDCramerRao
        (4 * blackHoleFarZoneBoseSpectralSusceptibility base) := by
  rw [blackHoleFarZoneBoseSpectralQuantumFisher_eq_four_mul_susceptibility]

/-- Every Hawking far-zone spectral model in the corpus has finite extended SLD error. -/
theorem blackHoleFarZone_extendedSLDCRB_ne_top (base : ℕ) :
    QuantumAlg.extendedScalarSLDCramerRao
        (blackHoleFarZoneBoseSpectralQuantumFisher base) ≠ ⊤ := by
  intro htop
  have hpos : 0 < blackHoleFarZoneBoseSpectralQuantumFisher base := by
    rw [blackHoleFarZoneBoseSpectralQuantumFisher_eq_four_mul_susceptibility]
    exact mul_pos (by norm_num) (blackHoleFarZoneBoseSpectralSusceptibility_pos base)
  exact (not_le_of_gt hpos)
    ((QuantumAlg.extendedScalarSLDCramerRao_eq_top_iff _).mp htop)

end

end RHTower
