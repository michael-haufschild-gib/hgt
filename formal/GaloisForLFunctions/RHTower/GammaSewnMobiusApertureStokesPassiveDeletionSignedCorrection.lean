import Mathlib.MeasureTheory.Measure.Sub
import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPositiveCompletionNoGo

/-!
# Passive deletion versus signed correction for the critical Stokes carrier

The raw reflected Stokes carrier has too much completed-source mass and first moment.  This file
extracts the strongest source-native correction visible before any all-degree comparison:

* both required correction moments are strictly negative in the signed response, so their
  magnitudes define a canonical positive one-atom two-jet countercarrier;
* subtracting that countercarrier repairs degrees zero and one exactly;
* a negative correction compatible with a positive final carrier is not a second architecture.
  It is precisely deletion/reweighting: `nu + delta = mu_raw`, equivalently `nu <= mu_raw`;
* either exact passive formulation already implies RH through the compact Markov capstone.

Thus signed correction survives unconditionally at the two-jet level. At all degrees the two
interfaces coincide. `GammaSewnMobiusApertureStokesCriticalPoleCapacity` subsequently proves both
impossible: every exact positive completion must increase infinitely many singleton masses, so
pure deletion cannot complete the source.
-/

open Complex Filter Function MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

noncomputable section
namespace RHTower

/-- Raw critical Stokes moment in the squared reciprocal-gap coordinate. -/
def gammaSewnMobiusApertureStokesCriticalRawMoment (n : ℕ) : ℝ :=
  ∫ y : ℝ, y ^ n ∂gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier

/-- Positive magnitude of the signed zeroth-order correction forced by the completed source. -/
def gammaSewnMobiusApertureStokesCriticalDeletedMass : ℝ :=
  gammaSewnMobiusApertureStokesCriticalRawMoment 0 - normalizedPrimeArchMoment 0

/-- Positive magnitude of the signed first-order correction forced by the completed source. -/
def gammaSewnMobiusApertureStokesCriticalDeletedFirstMoment : ℝ :=
  gammaSewnMobiusApertureStokesCriticalRawMoment 1 - normalizedPrimeArchMoment 1

theorem gammaSewnMobiusApertureStokesCriticalDeletedMass_pos :
    0 < gammaSewnMobiusApertureStokesCriticalDeletedMass := by
  unfold gammaSewnMobiusApertureStokesCriticalDeletedMass
    gammaSewnMobiusApertureStokesCriticalRawMoment
  linarith [normalizedPrimeArchMoment_zero_lt_integral_criticalSquaredCompactCarrier]

theorem gammaSewnMobiusApertureStokesCriticalDeletedFirstMoment_pos :
    0 < gammaSewnMobiusApertureStokesCriticalDeletedFirstMoment := by
  unfold gammaSewnMobiusApertureStokesCriticalDeletedFirstMoment
    gammaSewnMobiusApertureStokesCriticalRawMoment
  linarith [normalizedPrimeArchMoment_one_lt_integral_criticalSquaredCompactCarrier]

/-- Unique positive node at which one deleted atom matches both forced correction moments. -/
def gammaSewnMobiusApertureStokesCriticalDeletedBarycenter : ℝ :=
  gammaSewnMobiusApertureStokesCriticalDeletedFirstMoment /
    gammaSewnMobiusApertureStokesCriticalDeletedMass

theorem gammaSewnMobiusApertureStokesCriticalDeletedBarycenter_pos :
    0 < gammaSewnMobiusApertureStokesCriticalDeletedBarycenter := by
  exact div_pos gammaSewnMobiusApertureStokesCriticalDeletedFirstMoment_pos
    gammaSewnMobiusApertureStokesCriticalDeletedMass_pos

/-- Canonical positive countercarrier whose subtraction repairs the first two source moments. -/
def gammaSewnMobiusApertureStokesCriticalTwoJetCountercarrier : Measure ℝ :=
  ENNReal.ofReal gammaSewnMobiusApertureStokesCriticalDeletedMass •
    Measure.dirac gammaSewnMobiusApertureStokesCriticalDeletedBarycenter

theorem integral_pow_gammaSewnMobiusApertureStokesCriticalTwoJetCountercarrier_zero :
    (∫ y : ℝ, y ^ 0
        ∂gammaSewnMobiusApertureStokesCriticalTwoJetCountercarrier) =
      gammaSewnMobiusApertureStokesCriticalDeletedMass := by
  rw [gammaSewnMobiusApertureStokesCriticalTwoJetCountercarrier,
    integral_smul_measure]
  simp [ENNReal.toReal_ofReal
    gammaSewnMobiusApertureStokesCriticalDeletedMass_pos.le]

theorem integral_pow_gammaSewnMobiusApertureStokesCriticalTwoJetCountercarrier_one :
    (∫ y : ℝ, y ^ 1
        ∂gammaSewnMobiusApertureStokesCriticalTwoJetCountercarrier) =
      gammaSewnMobiusApertureStokesCriticalDeletedFirstMoment := by
  rw [gammaSewnMobiusApertureStokesCriticalTwoJetCountercarrier,
    integral_smul_measure]
  simp only [integral_dirac, pow_one, smul_eq_mul,
    ENNReal.toReal_ofReal
      gammaSewnMobiusApertureStokesCriticalDeletedMass_pos.le]
  rw [gammaSewnMobiusApertureStokesCriticalDeletedBarycenter]
  field_simp [gammaSewnMobiusApertureStokesCriticalDeletedMass_pos.ne']

/-- The canonical negative countercarrier repairs the completed zeroth source moment exactly. -/
theorem gammaSewnMobiusApertureStokesCriticalRaw_sub_twoJetCountercarrier_zero :
    gammaSewnMobiusApertureStokesCriticalRawMoment 0 -
        (∫ y : ℝ, y ^ 0
          ∂gammaSewnMobiusApertureStokesCriticalTwoJetCountercarrier) =
      normalizedPrimeArchMoment 0 := by
  rw [integral_pow_gammaSewnMobiusApertureStokesCriticalTwoJetCountercarrier_zero]
  unfold gammaSewnMobiusApertureStokesCriticalDeletedMass
  ring

/-- The same countercarrier repairs the completed first source moment exactly. -/
theorem gammaSewnMobiusApertureStokesCriticalRaw_sub_twoJetCountercarrier_one :
    gammaSewnMobiusApertureStokesCriticalRawMoment 1 -
        (∫ y : ℝ, y ^ 1
          ∂gammaSewnMobiusApertureStokesCriticalTwoJetCountercarrier) =
      normalizedPrimeArchMoment 1 := by
  rw [integral_pow_gammaSewnMobiusApertureStokesCriticalTwoJetCountercarrier_one]
  unfold gammaSewnMobiusApertureStokesCriticalDeletedFirstMoment
  ring

/-! ## Passive all-degree architecture classification -/

/-- Exact passive completion obtained by deleting/reweighting raw critical Stokes mass. -/
def GammaSewnMobiusApertureStokesCriticalPassiveDeletionCompletion : Prop :=
  ∃ (ν : Measure ℝ) (B : ℝ),
    IsFiniteMeasure ν ∧
    0 < B ∧
    (∀ᵐ x : ℝ ∂ν, 0 ≤ x ∧ |x| ≤ B) ∧
    ν ≤ gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier ∧
    completedSeamMomentGerm =ᶠ[nhds 0] compactMarkovTransform ν

/-- Exact negative correction retaining a positive final carrier.  The equation
`ν + δ = μraw` means that the signed response is `μraw - δ = ν`. -/
def GammaSewnMobiusApertureStokesCriticalPassiveNegativeCorrectionCompletion : Prop :=
  ∃ (ν δ : Measure ℝ) (B : ℝ),
    IsFiniteMeasure ν ∧
    0 < B ∧
    (∀ᵐ x : ℝ ∂ν, 0 ≤ x ∧ |x| ≤ B) ∧
    ν + δ = gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier ∧
    completedSeamMomentGerm =ᶠ[nhds 0] compactMarkovTransform ν

/-- **Signed/deletion collapse.** A negative correction compatible with passive positivity is
exactly a deletion/reweighting of the raw critical carrier.  It is not an independent route. -/
theorem gammaSewnMobiusApertureStokesCriticalPassiveNegativeCorrection_iff_deletion :
    GammaSewnMobiusApertureStokesCriticalPassiveNegativeCorrectionCompletion ↔
      GammaSewnMobiusApertureStokesCriticalPassiveDeletionCompletion := by
  constructor
  · rintro ⟨ν, δ, B, hfinite, hB, hsupport, hsum, hgerm⟩
    refine ⟨ν, B, hfinite, hB, hsupport, ?_, hgerm⟩
    calc
      ν ≤ ν + δ := Measure.le_add_right (le_refl ν)
      _ = gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier := hsum
  · rintro ⟨ν, B, hfinite, hB, hsupport, hle, hgerm⟩
    letI : IsFiniteMeasure ν := hfinite
    refine ⟨ν,
      gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier - ν,
      B, hfinite, hB, hsupport, ?_, hgerm⟩
    rw [add_comm]
    exact Measure.sub_add_cancel_of_le hle

/-- Any exact passive deletion producer closes RH; supplying it as a premise is circular. -/
theorem riemannHypothesis_of_gammaSewnMobiusApertureStokesCriticalPassiveDeletionCompletion
    (h : GammaSewnMobiusApertureStokesCriticalPassiveDeletionCompletion) :
    RiemannHypothesis := by
  obtain ⟨ν, B, hfinite, hB, hsupport, _hle, hgerm⟩ := h
  exact riemannHypothesis_of_primeArchCompactMarkovGermRepresentation
    ⟨ν, B, hfinite, hB, hsupport, hgerm⟩

/-- The passive signed-correction formulation closes RH for the same reason and no weaker one. -/
theorem riemannHypothesis_of_gammaSewnMobiusApertureStokesCriticalPassiveNegativeCorrectionCompletion
    (h : GammaSewnMobiusApertureStokesCriticalPassiveNegativeCorrectionCompletion) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_gammaSewnMobiusApertureStokesCriticalPassiveDeletionCompletion
    (gammaSewnMobiusApertureStokesCriticalPassiveNegativeCorrection_iff_deletion.mp h)

end RHTower
