import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalMassNoGo

/-!
# Positive-completion no-go for the reflected critical Stokes carrier

Reflection repairs the parity failure of the one-sided Stokes response, but the raw critical
squared carrier already has more zeroth moment than the completed prime--Gamma seam.  This file
closes the whole positive-extension class: no finite positive measure containing that raw carrier
can represent the completed seam Markov germ.

Consequently an exact repair must fail measure domination.  It must delete or reweight physical
Stokes atoms, or introduce a signed negative correction; adding further positive Hermitian sectors
cannot complete the C1 passive architecture.
-/

open Complex Filter Function MeasureTheory Set TopologicalSpace

noncomputable section
namespace RHTower

/-- A finite positive completed-seam carrier retaining every raw critical reflected Stokes atom. -/
def GammaSewnMobiusApertureStokesCriticalPositiveSupercarrierCompletion : Prop :=
  ∃ μ : Measure ℝ,
    IsFiniteMeasure μ ∧
    gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier ≤ μ ∧
    completedSeamMomentGerm =ᶠ[nhds 0] compactMarkovTransform μ

/-- Any finite positive measure containing the raw critical Stokes carrier has too much central
mass to represent the completed seam germ. -/
theorem not_completedSeamMomentGerm_eq_compactMarkov_of_criticalStokes_le
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hdom : gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier ≤ μ) :
    ¬ completedSeamMomentGerm =ᶠ[nhds 0] compactMarkovTransform μ := by
  intro hgerm
  letI : IsFiniteMeasure gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier :=
    gammaSewnMobiusApertureStokesSquaredCompactCarrier_finite
      (s := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hmass :=
    normalizedPrimeArchMoment_zero_eq_measureReal_univ_of_compactMarkovGerm μ hgerm
  have hraw : normalizedPrimeArchMoment 0 <
      gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier.real Set.univ := by
    simpa [MeasureTheory.integral_const] using
      normalizedPrimeArchMoment_zero_lt_integral_criticalSquaredCompactCarrier
  have hmeasure :
      gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier Set.univ ≤ μ Set.univ :=
    hdom Set.univ
  have hreal :
      gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier.real Set.univ ≤
        μ.real Set.univ := by
    rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top μ Set.univ) hmeasure
  linarith

/-- Exact survivor constraint: every finite positive completed-seam carrier must omit positive mass
from the raw critical Stokes carrier. -/
theorem criticalStokes_not_le_of_completedSeamMomentGerm_eq_compactMarkov
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hgerm : completedSeamMomentGerm =ᶠ[nhds 0] compactMarkovTransform μ) :
    ¬ gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier ≤ μ := by
  intro hdom
  exact not_completedSeamMomentGerm_eq_compactMarkov_of_criticalStokes_le μ hdom hgerm

/-- **Closed architecture no-go.** No finite positive Hermitian extension retaining the raw
critical reflected Stokes carrier can equal the completed prime--Gamma seam germ. -/
theorem not_gammaSewnMobiusApertureStokesCriticalPositiveSupercarrierCompletion :
    ¬ GammaSewnMobiusApertureStokesCriticalPositiveSupercarrierCompletion := by
  rintro ⟨μ, hfinite, hdom, hgerm⟩
  letI : IsFiniteMeasure μ := hfinite
  exact not_completedSeamMomentGerm_eq_compactMarkov_of_criticalStokes_le μ hdom hgerm

end RHTower
