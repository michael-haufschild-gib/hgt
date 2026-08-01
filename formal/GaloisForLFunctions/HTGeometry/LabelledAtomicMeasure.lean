import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Sub

/-!
# The labelled atomic measure and its residual

A cofinal spectral limit decomposes as a labelled atomic survivor plus a residual.  The survivor is
the measure carried by the labelled points with the surviving masses; the residual is what is left.

Its total mass is exactly the labelled mass deficit: a probability limit minus a labelled part of
total mass `sum p_k` leaves residual mass `1 - sum p_k`.  Nothing here needs the labels to be
distinct or the masses to be positive.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {ι X : Type*} [MeasurableSpace X]

/-- The labelled atomic measure: mass `p k` placed at the label `u k`. -/
noncomputable def labelledMeasure (p : ι → ENNReal) (u : ι → X) : Measure X :=
  Measure.sum fun k => p k • Measure.dirac (u k)

/-- Its total mass is the total labelled mass. -/
theorem labelledMeasure_univ (p : ι → ENNReal) (u : ι → X) :
    labelledMeasure p u Set.univ = ∑' k, p k := by
  rw [labelledMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp

/-- A labelled part below a finite measure is itself finite. -/
theorem isFiniteMeasure_labelledMeasure {p : ι → ENNReal} {u : ι → X} {σ : Measure X}
    [IsFiniteMeasure σ] (hle : labelledMeasure p u ≤ σ) :
    IsFiniteMeasure (labelledMeasure p u) := by
  constructor
  exact lt_of_le_of_lt (hle Set.univ) (measure_lt_top σ Set.univ)

/-- **`(21)`.**  The residual of a probability limit over its labelled part carries exactly the
labelled mass deficit. -/
theorem residual_univ_eq {p : ι → ENNReal} {u : ι → X} {σ : Measure X}
    [IsProbabilityMeasure σ] (hle : labelledMeasure p u ≤ σ) :
    (σ - labelledMeasure p u) Set.univ = 1 - ∑' k, p k := by
  haveI := isFiniteMeasure_labelledMeasure hle
  rw [Measure.sub_apply MeasurableSet.univ hle, labelledMeasure_univ, measure_univ]

/-- **`(22)`.**  The limit is the labelled atomic survivor plus the residual. -/
theorem labelled_add_residual {p : ι → ENNReal} {u : ι → X} {σ : Measure X}
    [IsFiniteMeasure σ] (hle : labelledMeasure p u ≤ σ) :
    (σ - labelledMeasure p u) + labelledMeasure p u = σ := by
  haveI := isFiniteMeasure_labelledMeasure hle
  exact Measure.sub_add_cancel_of_le hle

/-- The residual vanishes exactly when the labelled masses exhaust the total. -/
theorem residual_eq_zero_iff {p : ι → ENNReal} {u : ι → X} {σ : Measure X}
    [IsProbabilityMeasure σ] (hle : labelledMeasure p u ≤ σ) :
    (σ - labelledMeasure p u) Set.univ = 0 ↔ 1 ≤ ∑' k, p k := by
  rw [residual_univ_eq hle, tsub_eq_zero_iff_le]

end GaloisForLFunctions.HTGeometry
