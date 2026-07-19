import GaloisForLFunctions.HTGeometry.NevLeafFunction

/-!
# The leaf of a parameter is unique

A probability measure that represents the moment sequence and is carried by a denominator fiber has
atoms at most `λ` there, and the `λ`'s on that fiber already sum to `1` — because the leaf itself is
carried there with exactly those atoms.  So the inequality is an equality termwise and the measure is
the leaf.

Uniqueness is what turns a compactness argument into a convergence argument: any weak limit of leaves
that represents the sequence and sits on the right fiber must *be* the leaf there.
-/

open scoped BigOperators
open MeasureTheory OnePoint
open scoped OnePoint

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The Christoffel weights on a finite-parameter fiber sum to exactly one. -/
theorem tsum_ofReal_christoffelLimit_fiber (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (tau : ℝ) :
    ∑' ξ : ↥((nevMatrixDataInf h h0b).finiteDenominatorFiber tau),
        ENNReal.ofReal (christoffelLimit s (ξ : ℝ)) = 1 := by
  set F := (nevMatrixDataInf h h0b).finiteDenominatorFiber tau with hF
  set μ : Measure ℝ := (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ) with hμ
  have hprob : IsProbabilityMeasure μ := inferInstance
  have hFm : MeasurableSet F := (isClosed_finiteDenominatorFiber h h0b tau).measurableSet
  have hFc : F.Countable := countable_finiteDenominatorFiber h h0b tau
  have hfull : μ F = 1 := by
    have h2 := measure_add_measure_compl (μ := μ) hFm
    rw [nevLeaf_finite_carried h h0b h0 tau, add_zero, measure_univ] at h2
    exact h2
  rw [measure_eq_tsum_singleton _ hFc] at hfull
  rw [← hfull]
  exact tsum_congr fun ξ => (nevLeaf_atoms h h0b h0 tau ξ.2).symm

/-- A weighted Dirac family only sees the weights on its own carrier. -/
theorem fiberMeasure_congr {w w' : ℝ → ℝ} {F : Set ℝ} (hww : ∀ x ∈ F, w x = w' x) :
    fiberMeasure w F = fiberMeasure w' F := by
  rw [fiberMeasure, fiberMeasure]
  exact congrArg Measure.sum (funext fun p => by rw [hww (p : ℝ) p.2])

/-- **Uniqueness of the leaf.**  A probability measure representing the sequence and carried by the
fiber of `τ` is the leaf of `τ`. -/
theorem nevLeaf_unique (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (tau : ℝ) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hmom : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s ν)
    (hcar : ν ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau)ᶜ = 0) :
    ν = (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ) := by
  set F := (nevMatrixDataInf h h0b).finiteDenominatorFiber tau with hF
  have hFm : MeasurableSet F := (isClosed_finiteDenominatorFiber h h0b tau).measurableSet
  have hFc : F.Countable := countable_finiteDenominatorFiber h h0b tau
  have hsum : ∑' ξ : ↥F, ENNReal.ofReal (christoffelLimit s (ξ : ℝ)) ≤ 1 :=
    le_of_eq (tsum_ofReal_christoffelLimit_fiber h h0b h0 tau)
  have hatoms : ∀ ξ : ↥F, ν {(ξ : ℝ)} = ENNReal.ofReal (christoffelLimit s (ξ : ℝ)) :=
    fun ξ => measure_singleton_eq_of_tsum_le h hmom hFc hFm hcar measure_univ hsum ξ
  have hν : ν = fiberMeasure (fun x => (ν {x}).toReal) F :=
    measure_eq_fiberMeasure_of_carried ν hFc hFm hcar
  rw [hν, nevLeaf_eq_fiberMeasure h h0b h0 tau]
  refine fiberMeasure_congr fun x hx => ?_
  rw [hatoms ⟨x, hx⟩, ENNReal.toReal_ofReal (christoffelLimit_nonneg h x)]

/-- **Uniqueness at the parameter infinity.** -/
theorem nevLeaf_infinity_unique (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hmom : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s ν)
    (hcar : ν (nevMatrixDataInf h h0b).infinityDenominatorFiberᶜ = 0) :
    ν = (nevLeaf h h0b h0 ∞ : Measure ℝ) := by
  set F := (nevMatrixDataInf h h0b).infinityDenominatorFiber with hF
  have hFm : MeasurableSet F := (isClosed_infinityDenominatorFiber h h0b).measurableSet
  have hFc : F.Countable := countable_infinityDenominatorFiber h h0b
  set μ : Measure ℝ := (nevLeaf h h0b h0 ∞ : Measure ℝ) with hμ
  have hprob : IsProbabilityMeasure μ := inferInstance
  have hfull : μ F = 1 := by
    have h2 := measure_add_measure_compl (μ := μ) hFm
    rw [nevLeaf_infinity_carried h h0b h0, add_zero, measure_univ] at h2
    exact h2
  rw [measure_eq_tsum_singleton _ hFc] at hfull
  have hsum : ∑' ξ : ↥F, ENNReal.ofReal (christoffelLimit s (ξ : ℝ)) ≤ 1 := by
    rw [← hfull]
    exact le_of_eq (tsum_congr fun ξ => (nevLeaf_infinity_atoms h h0b h0 ξ.2).symm)
  have hatoms : ∀ ξ : ↥F, ν {(ξ : ℝ)} = ENNReal.ofReal (christoffelLimit s (ξ : ℝ)) :=
    fun ξ => measure_singleton_eq_of_tsum_le h hmom hFc hFm hcar measure_univ hsum ξ
  have hνeq : ν = fiberMeasure (fun x => (ν {x}).toReal) F :=
    measure_eq_fiberMeasure_of_carried ν hFc hFm hcar
  have hμeq : μ = fiberMeasure (fun x => (μ {x}).toReal) F :=
    measure_eq_fiberMeasure_of_carried μ hFc hFm (nevLeaf_infinity_carried h h0b h0)
  rw [hνeq, hμeq]
  refine fiberMeasure_congr fun x hx => ?_
  rw [hatoms ⟨x, hx⟩, nevLeaf_infinity_atoms h h0b h0 hx]

end HTGeometry
