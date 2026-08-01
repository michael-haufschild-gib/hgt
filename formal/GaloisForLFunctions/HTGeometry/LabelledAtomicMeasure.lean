import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Integral.Bochner.Basic

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

/-- **Testing the labelled measure is summing the labelled series.**  Integrating against the
labelled atomic measure is exactly the labelled sum of the test values.

This is the bridge between the measure-level and series-level descriptions: whatever transform one
takes of a labelled atomic measure — Donoghue, Cauchy, or any other kernel — its value is the
corresponding series.  So a spectral-measure sum identity reduces to identifying the measure. -/
theorem integral_labelledMeasure [MeasurableSingletonClass X] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (p : ι → ENNReal) (u : ι → X) (f : X → E)
    (hf : Integrable f (labelledMeasure p u)) :
    ∫ x, f x ∂(labelledMeasure p u) = ∑' k, (p k).toReal • f (u k) := by
  rw [labelledMeasure] at hf ⊢
  rw [integral_sum_measure hf]
  refine tsum_congr fun k => ?_
  rw [integral_smul_measure, integral_dirac]

/-! ## The two defects

Failure of the tight pure-point criterion separates into exactly two independent defects: mass that
never gets labelled, and labels that escape to the boundary.  The separation is sharp because the
two constraints — total mass at most one, labels within the closed window — are each saturated in
exactly one of the two failure modes. -/

/-- **`(26)`.**  Failure of the criterion `sum p_k = 1` together with `|u_k| < b` is exactly:
either unlabelled residual mass, or a label reaching the boundary. -/
theorem tight_criterion_failure_iff {ι : Type*} {p : ι → ℝ} {u : ι → ℝ} {b : ℝ}
    (hp : ∑' k, p k ≤ 1) (hu : ∀ k, |u k| ≤ b) :
    ¬((∑' k, p k = 1) ∧ ∀ k, |u k| < b) ↔ ((∑' k, p k < 1) ∨ ∃ k, |u k| = b) := by
  constructor
  · intro h
    by_cases hs : ∑' k, p k = 1
    · right
      by_contra hc
      exact h ⟨hs, fun k => lt_of_le_of_ne (hu k) fun heq => hc ⟨k, heq⟩⟩
    · left
      exact lt_of_le_of_ne hp hs
  · rintro (h | ⟨k, hk⟩) ⟨hs, hlt⟩
    · linarith
    · exact absurd hk (ne_of_lt (hlt k))

/-- The two defects are independent: neither implies the other.  Unlabelled mass can occur with
every label interior, and a boundary label can occur with full labelled mass. -/
theorem two_defects_independent {b : ℝ} (hb : 0 < b) :
    (∃ (p : Unit → ℝ) (u : Unit → ℝ), (∑' k, p k < 1) ∧ (∀ k, |u k| < b)) ∧
      (∃ (p : Unit → ℝ) (u : Unit → ℝ), (∑' k, p k = 1) ∧ ∃ k, |u k| = b) := by
  constructor
  · refine ⟨fun _ => 0, fun _ => 0, ?_, ?_⟩
    · simp
    · simpa using hb
  · refine ⟨fun _ => 1, fun _ => b, ?_, ⟨(), ?_⟩⟩
    · simp
    · rw [abs_of_pos hb]

/-- Coalescence of two labels is a third, separate failure: the labelled divisor stops being
simple, with no mass lost and no label escaping. -/
theorem coalescence_not_injective {ι : Type*} {u : ι → ℝ} {j k : ι}
    (hjk : j ≠ k) (heq : u j = u k) : ¬ Function.Injective u :=
  fun hinj => hjk (hinj heq)

end GaloisForLFunctions.HTGeometry
