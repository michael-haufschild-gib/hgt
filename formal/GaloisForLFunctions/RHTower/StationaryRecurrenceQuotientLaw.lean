import GaloisForLFunctions.RHTower.ObserverRecurrenceDistributionLaw

/-!
# The stationary recurrence quotient law

Every survival-return experiment on a stationary quantum spectrum factors
through two canonical information quotients:

* the system spectrum is replaced by its energy-difference law;
* the clock law is replaced by its reflection-even orientation quotient.

The theorem below identifies the complete sampled return probability law
with the pushforward pairing of exactly these two quotients.  It applies to
arbitrary real probability spectra and arbitrary probability clocks.
-/

open MeasureTheory

namespace RHTower

noncomputable section

/-- The survival fidelity carried by the system's energy-difference law. -/
def recurrenceQuotientFidelity
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (t : ℝ) : ℝ :=
  (charFun (spectralDifferenceMeasure mu) t).re

/-- Probability-law pairing of the maximal system and clock recurrence
quotients. -/
def recurrenceQuotientProbabilityMeasure
    (clockLaw : ProbabilityMeasure ℝ)
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    (clockOrientationQuotientLaw clockLaw)
    (f := recurrenceQuotientFidelity mu)
    (by
      exact
        (Complex.continuous_re.comp
          continuous_charFun).aemeasurable)

/-- The quotient fidelity is exactly the original survival fidelity. -/
theorem recurrenceQuotientFidelity_eq_normSq_charFun
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (t : ℝ) :
    recurrenceQuotientFidelity mu t =
      Complex.normSq (charFun mu t) := by
  rw [recurrenceQuotientFidelity,
    charFun_spectralDifferenceMeasure]
  simp

/-- **Universal stationary recurrence quotient law.**  For every
probability energy spectrum and every probability clock, the complete
sampled survival-return distribution is the pushforward of the clock's
orientation quotient by the characteristic function of the system's
energy-difference law. -/
theorem clockSampledSpectralReturnProbabilityMeasure_eq_recurrenceQuotient
    (clockLaw : ProbabilityMeasure ℝ)
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    (clockSampledSpectralReturnProbabilityMeasure
        clockLaw mu : Measure ℝ) =
      (recurrenceQuotientProbabilityMeasure
        clockLaw mu : Measure ℝ) := by
  have horientation :
      (clockSampledSpectralReturnProbabilityMeasure
          clockLaw mu : Measure ℝ) =
        (clockSampledSpectralReturnProbabilityMeasure
          (clockOrientationQuotientLaw clockLaw) mu :
            Measure ℝ) := by
    apply
      (clockSampledSpectralReturnProbabilityMeasure_eq_iff_moments
        clockLaw (clockOrientationQuotientLaw clockLaw)
        mu mu).2
    intro n
    rw [clockSampledSpectralReturnMoment_orientationQuotient]
  rw [horientation]
  rw [clockSampledSpectralReturnProbabilityMeasure,
    recurrenceQuotientProbabilityMeasure,
    ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_map]
  apply Measure.map_congr
  filter_upwards with t
  exact (recurrenceQuotientFidelity_eq_normSq_charFun
    mu t).symm

end

end RHTower
