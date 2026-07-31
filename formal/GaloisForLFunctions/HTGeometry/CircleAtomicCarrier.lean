import GaloisForLFunctions.HTGeometry.CircleSingularWitness
import Mathlib.MeasureTheory.Measure.Support

/-!
# A finite circle measure with infinite support, singular to Lebesgue

The pure-singular carrier layer is stated for a finite circle measure that is singular to
`circleLebesgue` **and** has infinite support.  Singularity is free for a countable carrier; infinite
support needs infinitely many atoms.  Both hold for the dyadic atomic measure concentrated on the
points `exp (1/(n+1))`.

* `support_infinite_of_injective` — infinitely many atoms of positive mass give infinite support;
* `circleAtomPoint_injective` — an explicit injective sequence on the circle;
* **`exists_pureSingularCarrier_circle`** — the joint witness.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology Real
open scoped ENNReal

noncomputable section

/-! ## Infinite support from infinitely many atoms -/

/-- A measure with infinitely many atoms of positive mass has infinite support. -/
theorem support_infinite_of_injective {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (mu : Measure X) {z : ℕ → X} (hz : Function.Injective z)
    (hpos : ∀ n, 0 < mu {z n}) : mu.support.Infinite := by
  have hsub : Set.range z ⊆ mu.support := by
    rintro _ ⟨n, rfl⟩
    rw [Measure.mem_support_iff_forall]
    intro U hU
    exact lt_of_lt_of_le (hpos n)
      (measure_mono (Set.singleton_subset_iff.mpr (mem_of_mem_nhds hU)))
  exact (Set.infinite_range_of_injective hz).mono hsub

/-! ## An injective sequence of circle points -/

/-- The circle points at angles `1/(n+1)`, all inside the principal branch. -/
def circleAtomPoint (n : ℕ) : Circle := Circle.exp (1 / (n + 1 : ℝ))

theorem arg_circleAtomPoint (n : ℕ) :
    Complex.arg (circleAtomPoint n : ℂ) = 1 / (n + 1 : ℝ) := by
  refine Circle.arg_exp ?_ ?_
  · have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    linarith [Real.pi_pos]
  · have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    linarith [Real.pi_gt_three]

theorem circleAtomPoint_injective : Function.Injective circleAtomPoint := by
  intro n m h
  have heq : 1 / ((n : ℝ) + 1) = 1 / ((m : ℝ) + 1) := by
    rw [← arg_circleAtomPoint n, ← arg_circleAtomPoint m, h]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have : ((n : ℝ) + 1) = ((m : ℝ) + 1) := by
    field_simp at heq
    linarith
  have : (n : ℝ) = (m : ℝ) := by linarith
  exact_mod_cast this

/-! ## The dyadic atomic carrier -/

/-- The probability measure putting mass `2⁻ⁿ⁻¹` on the `n`-th circle point. -/
def circleAtomicMeasure : Measure Circle :=
  Measure.sum fun n : ℕ => (2⁻¹ : ℝ≥0∞) ^ (n + 1) • Measure.dirac (circleAtomPoint n)

theorem circleAtomicMeasure_apply {s : Set Circle} (hs : MeasurableSet s) :
    circleAtomicMeasure s =
      ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + 1) * Measure.dirac (circleAtomPoint n) s := by
  rw [circleAtomicMeasure, Measure.sum_apply _ hs]
  simp

theorem circleAtomicMeasure_univ : circleAtomicMeasure Set.univ = 1 := by
  rw [circleAtomicMeasure_apply MeasurableSet.univ]
  simp only [measure_univ, mul_one]
  rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two,
    ENNReal.mul_inv_cancel (by simp) (by simp)]

instance : IsProbabilityMeasure circleAtomicMeasure := ⟨circleAtomicMeasure_univ⟩

theorem circleAtomicMeasure_singleton_pos (n : ℕ) :
    0 < circleAtomicMeasure {circleAtomPoint n} := by
  have hle : (2⁻¹ : ℝ≥0∞) ^ (n + 1) *
      Measure.dirac (circleAtomPoint n) {circleAtomPoint n} ≤
      circleAtomicMeasure {circleAtomPoint n} := by
    rw [circleAtomicMeasure_apply (measurableSet_singleton _)]
    exact ENNReal.le_tsum n
  refine lt_of_lt_of_le ?_ hle
  rw [Measure.dirac_apply_of_mem (Set.mem_singleton _), mul_one]
  exact ENNReal.pow_pos (by norm_num) _

theorem circleAtomicMeasure_mutuallySingular :
    circleAtomicMeasure ⟂ₘ circleLebesgue := by
  have hmeas : MeasurableSet ((Set.range circleAtomPoint)ᶜ) :=
    (Set.countable_range circleAtomPoint).measurableSet.compl
  refine mutuallySingular_circleLebesgue_of_countable
    (s := Set.range circleAtomPoint) (Set.countable_range _) ?_
  rw [circleAtomicMeasure_apply hmeas]
  refine (tsum_congr fun n => ?_).trans tsum_zero
  rw [Measure.dirac_apply' _ hmeas, Set.indicator_of_notMem (by simp), mul_zero]

/-- **A pure singular circle carrier exists.**  The dyadic atomic measure is a probability measure,
singular to circle Lebesgue measure, with infinite support. -/
theorem exists_pureSingularCarrier_circle :
    ∃ mu : Measure Circle, IsProbabilityMeasure mu ∧ mu ⟂ₘ circleLebesgue ∧
      mu.support.Infinite :=
  ⟨circleAtomicMeasure, inferInstance, circleAtomicMeasure_mutuallySingular,
    support_infinite_of_injective circleAtomicMeasure circleAtomPoint_injective
      circleAtomicMeasure_singleton_pos⟩

end

end GaloisForLFunctions.HTGeometry
