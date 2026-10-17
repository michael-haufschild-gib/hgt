import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Finite positive atomic measures and their test integrals

Explicit positive Dirac packets have exact test integrals and atom masses. A positive total
weight yields a probability measure after normalization.
-/

open MeasureTheory
open scoped BigOperators NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite sum of weighted Dirac masses. Negative weights are clamped to zero. -/
def finiteRealAtomicMeasure {α ι : Type*} [MeasurableSpace α]
    (s : Finset ι) (x : ι → α) (w : ι → ℝ) : FiniteMeasure α :=
  ⟨∑ i ∈ s, (Real.toNNReal (w i)) • Measure.dirac (x i), by infer_instance⟩

theorem integral_finiteRealAtomicMeasure {α ι : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (s : Finset ι) (x : ι → α) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (f : α → ℝ) :
    (∫ y, f y ∂(finiteRealAtomicMeasure s x w : Measure α)) =
      ∑ i ∈ s, w i * f (x i) := by
  change (∫ y, f y ∂(∑ i ∈ s, (Real.toNNReal (w i)) • Measure.dirac (x i))) = _
  rw [integral_finsetSum_measure (by
    intro i hi
    exact (integrable_dirac (by finiteness)).smul_measure_nnreal)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_smul_nnreal_measure, integral_dirac]
  change (Real.toNNReal (w i) : ℝ) * f (x i) = w i * f (x i)
  rw [Real.coe_toNNReal _ (hw i hi)]

theorem real_finiteRealAtomicMeasure_apply {α ι : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (s : Finset ι) (x : ι → α) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) {A : Set α}
    [DecidablePred (fun i => x i ∈ A)] (hA : MeasurableSet A) :
    (finiteRealAtomicMeasure s x w : Measure α).real A =
      ∑ i ∈ s with x i ∈ A, w i := by
  classical
  rw [← integral_indicator_one hA,
    integral_finiteRealAtomicMeasure s x w hw]
  simp only [Set.indicator_apply, Pi.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_filter]

/-- Normalize a finite positive atomic packet by its total weight. -/
def normalizedFiniteRealAtomicMeasure {α ι : Type*} [MeasurableSpace α]
    (s : Finset ι) (x : ι → α) (w : ι → ℝ) : FiniteMeasure α :=
  finiteRealAtomicMeasure s x (fun i => w i / ∑ j ∈ s, w j)

theorem isProbabilityMeasure_normalizedFiniteRealAtomicMeasure
    {α ι : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (s : Finset ι) (x : ι → α) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hpos : 0 < ∑ i ∈ s, w i) :
    IsProbabilityMeasure (normalizedFiniteRealAtomicMeasure s x w : Measure α) := by
  apply isProbabilityMeasure_iff_real.mpr
  rw [normalizedFiniteRealAtomicMeasure, real_finiteRealAtomicMeasure_apply
    s x _ (fun i hi => div_nonneg (hw i hi) hpos.le) MeasurableSet.univ]
  simp only [Set.mem_univ, Finset.filter_true]
  rw [← Finset.sum_div, div_self hpos.ne']

theorem integral_normalizedFiniteRealAtomicMeasure
    {α ι : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (s : Finset ι) (x : ι → α) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hpos : 0 < ∑ i ∈ s, w i) (f : α → ℝ) :
    (∫ y, f y ∂(normalizedFiniteRealAtomicMeasure s x w : Measure α)) =
      (∑ i ∈ s, w i * f (x i)) / ∑ i ∈ s, w i := by
  rw [normalizedFiniteRealAtomicMeasure, integral_finiteRealAtomicMeasure
    s x _ (fun i hi => div_nonneg (hw i hi) hpos.le), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end
end GaloisForLFunctions.HTGeometry
