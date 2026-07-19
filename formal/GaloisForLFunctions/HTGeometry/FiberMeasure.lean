import GaloisForLFunctions.HTGeometry.NevFiberCountable
import GaloisForLFunctions.HTGeometry.CountableWeightedDirac

/-!
# Measures carried by a countable fiber

A leaf of the extremal family is a weighted sum of point masses on a denominator fiber.  Indexing the
sum by the fiber itself, rather than by an enumeration of it, makes the construction independent of
any choice of listing and makes carriedness immediate: every point mass sits at a point of the fiber,
so the complement is null whatever the weights are.

The weights are `christoffelLimit`, the classical N-extremal weight.

`Measure.sum` and its evaluation lemmas hold for an arbitrary index type, so none of the general
results here need the fiber to be countable; countability enters only where a listing is wanted.
-/

open scoped BigOperators
open MeasureTheory

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The weighted sum of point masses over a set, indexed by the set itself. -/
noncomputable def fiberMeasure (w : ℝ → ℝ) (F : Set ℝ) : Measure ℝ :=
  Measure.sum fun p : ↥F => ENNReal.ofReal (w (p : ℝ)) • Measure.dirac (p : ℝ)

theorem fiberMeasure_apply (w : ℝ → ℝ) (F : Set ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    fiberMeasure w F A = ∑' p : ↥F, ENNReal.ofReal (w (p : ℝ)) * A.indicator 1 (p : ℝ) := by
  rw [fiberMeasure, Measure.sum_apply _ hA]
  refine tsum_congr fun p => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]

/-- **Lower integration against the fiber measure.** -/
theorem lintegral_fiberMeasure (w : ℝ → ℝ) (F : Set ℝ) (f : ℝ → ENNReal) :
    ∫⁻ y, f y ∂(fiberMeasure w F) = ∑' p : ↥F, ENNReal.ofReal (w (p : ℝ)) * f (p : ℝ) := by
  rw [fiberMeasure, lintegral_sum_measure]
  refine tsum_congr fun p => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-- **The fiber measure is carried by the fiber**, whatever the weights are. -/
theorem fiberMeasure_compl_eq_zero (w : ℝ → ℝ) {F : Set ℝ}
    (hFm : MeasurableSet F) : fiberMeasure w F Fᶜ = 0 := by
  rw [fiberMeasure_apply w F hFm.compl]
  have hterm : ∀ p : ↥F, ENNReal.ofReal (w (p : ℝ)) * Fᶜ.indicator 1 (p : ℝ) = 0 := by
    intro p
    rw [Set.indicator_of_notMem (by simp), mul_zero]
  rw [tsum_congr hterm, tsum_zero]

/-- The atom at a point of the fiber is its weight. -/
theorem fiberMeasure_singleton (w : ℝ → ℝ) {F : Set ℝ} {x : ℝ} (hx : x ∈ F) :
    fiberMeasure w F {x} = ENNReal.ofReal (w x) := by
  rw [fiberMeasure_apply w F (measurableSet_singleton x), tsum_eq_single ⟨x, hx⟩]
  · rw [Set.indicator_of_mem (Set.mem_singleton x)]
    simp
  · intro p hp
    rw [Set.indicator_of_notMem, mul_zero]
    simp only [Set.mem_singleton_iff]
    exact fun hc => hp (Subtype.ext hc)

/-- **The candidate N-extremal leaf at a finite parameter**: the Christoffel weights on the
denominator fiber. -/
noncomputable def nevLeafFinite (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (tau : ℝ) : Measure ℝ :=
  fiberMeasure (christoffelLimit s) ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau)

/-- **The candidate N-extremal leaf at the parameter at infinity.** -/
noncomputable def nevLeafInfinity (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    Measure ℝ :=
  fiberMeasure (christoffelLimit s) (nevMatrixDataInf h h0b).infinityDenominatorFiber

/-- **The `finite_carried` content**: the finite-parameter leaf is carried by its denominator
fiber. -/
theorem nevLeafFinite_carried (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (tau : ℝ) :
    nevLeafFinite h h0b tau ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau)ᶜ = 0 :=
  fiberMeasure_compl_eq_zero _ (isClosed_finiteDenominatorFiber h h0b tau).measurableSet

/-- **The `infinity_carried` content**: the leaf at infinity is carried by its denominator fiber. -/
theorem nevLeafInfinity_carried (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    nevLeafInfinity h h0b (nevMatrixDataInf h h0b).infinityDenominatorFiberᶜ = 0 :=
  fiberMeasure_compl_eq_zero _ (isClosed_infinityDenominatorFiber h h0b).measurableSet

/-- Each atom of the finite-parameter leaf is the Christoffel limit at that node. -/
theorem nevLeafFinite_singleton (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (tau : ℝ)
    {x : ℝ} (hx : x ∈ (nevMatrixDataInf h h0b).finiteDenominatorFiber tau) :
    nevLeafFinite h h0b tau {x} = ENNReal.ofReal (christoffelLimit s x) :=
  fiberMeasure_singleton _ hx

end HTGeometry
