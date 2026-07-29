import GaloisForLFunctions.RHTower.ObserverTemporalUniversalityLaw
import GaloisForLFunctions.RHTower.ObserverRecurrenceDistributionLaw

/-!
# The observer-time gap measure

The projective return record of an arbitrary probability energy spectrum is
not merely computed from its energy-difference measure.  It is the
characteristic function of that measure, so characteristic-function
uniqueness makes the two objects equivalent: the complete fidelity record
determines exactly one gap measure and nothing finer.

That same measure controls exact recurrence through its support-generated
frequency group and all long-time return moments through additive convolution
collisions.  It is invariant under the unobservable choice of energy origin.
-/

open Complex Filter MeasureTheory Set Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open SpectralMemory

/-- Projective energy-gap law carried by an observer's spectral probability
measure. -/
def observerTimeGapMeasure (mu : Measure ℝ) : Measure ℝ :=
  spectralDifferenceMeasure mu

/-- Complete projective return-fidelity record. -/
def projectiveReturnRecord (mu : Measure ℝ) (t : ℝ) : ℝ :=
  Complex.normSq (charFun mu t)

/-- Return fidelity is exactly the characteristic function of the
observer-time gap measure. -/
theorem charFun_observerTimeGapMeasure
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (t : ℝ) :
    charFun (observerTimeGapMeasure mu) t =
      (projectiveReturnRecord mu t : ℂ) := by
  exact charFun_spectralDifferenceMeasure mu t

/-- **Complete observer-time factorization.**  Two arbitrary probability
spectra have identical projective return records at every time if and only if
their observer-time gap measures are identical.  This includes discrete,
continuous, mixed, finite, and infinite spectra without additional spectral
hypotheses. -/
theorem observerTimeGapMeasure_eq_iff_projectiveReturnRecord_eq
    (mu nu : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    observerTimeGapMeasure mu = observerTimeGapMeasure nu ↔
      ∀ t : ℝ,
        projectiveReturnRecord mu t =
          projectiveReturnRecord nu t := by
  constructor
  · intro h t
    have hchar := congrArg (fun rho : Measure ℝ => charFun rho t) h
    change charFun (observerTimeGapMeasure mu) t =
      charFun (observerTimeGapMeasure nu) t at hchar
    rw [charFun_observerTimeGapMeasure,
      charFun_observerTimeGapMeasure] at hchar
    exact_mod_cast hchar
  · intro h
    letI : IsProbabilityMeasure (observerTimeGapMeasure mu) := by
      unfold observerTimeGapMeasure
      infer_instance
    letI : IsProbabilityMeasure (observerTimeGapMeasure nu) := by
      unfold observerTimeGapMeasure
      infer_instance
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_observerTimeGapMeasure,
      charFun_observerTimeGapMeasure]
    exact_mod_cast h t

/-- The observer-time gap measure is projective: shifting every energy by an
arbitrary common constant does not alter it. -/
theorem observerTimeGapMeasure_translate_invariant
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (c : ℝ) :
    observerTimeGapMeasure (translateObserverSpectrum mu c) =
      observerTimeGapMeasure mu :=
  spectralDifferenceMeasure_translateObserverSpectrum mu c

/-- Equality of the complete projective return records is equivalent to
equality of the entire additive collision hierarchy, not only its scalar
moments. -/
theorem projectiveReturnRecord_eq_iff_collisionMeasures_eq
    (mu nu : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    (∀ t : ℝ,
        projectiveReturnRecord mu t =
          projectiveReturnRecord nu t) ↔
      ∀ n : ℕ,
        convPow (observerTimeGapMeasure mu) n =
          convPow (observerTimeGapMeasure nu) n := by
  constructor
  · intro h n
    rw [(observerTimeGapMeasure_eq_iff_projectiveReturnRecord_eq
      mu nu).2 h]
  · intro h
    apply (observerTimeGapMeasure_eq_iff_projectiveReturnRecord_eq
      mu nu).1
    letI : IsProbabilityMeasure (observerTimeGapMeasure mu) := by
      unfold observerTimeGapMeasure
      infer_instance
    letI : IsProbabilityMeasure (observerTimeGapMeasure nu) := by
      unfold observerTimeGapMeasure
      infer_instance
    simpa only [convPow,
      MeasureTheory.Measure.conv_dirac_zero] using h 1

/-- A positive exact projective return exists exactly in the cyclic
support-group phase of the observer-time gap measure. -/
theorem exists_positive_projectiveReturnRecord_one_iff_cyclic
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    (∃ t : ℝ, 0 < t ∧ projectiveReturnRecord mu t = 1) ↔
      ∃ omega : ℝ,
        measureVisibleFrequencyGroup (observerTimeGapMeasure mu) =
          AddSubgroup.zmultiples omega := by
  exact exists_positive_unitFidelity_iff_cyclic mu

/-- Every long-time return moment is the zero-sum collision mass of the
corresponding convolution power of the same observer-time gap measure. -/
theorem spectralReturnMomentMeanReal_tendsto_observerTimeCollisions
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (n : ℕ) :
    Tendsto (spectralReturnMomentMeanReal mu n) atTop
      (𝓝 ((convPow (observerTimeGapMeasure mu) n).real {0})) := by
  exact spectralReturnMomentMeanReal_tendsto_collisionHierarchy mu n

end RHTower
