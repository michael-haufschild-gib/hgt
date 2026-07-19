import GaloisForLFunctions.HTGeometry.FiberWeightSum
import GaloisForLFunctions.HTGeometry.FiberMeasure

/-!
# A measure carried by a countable set is its own atomic part

If `μ` gives the complement of a countable `F` no mass then `μ` is exactly the weighted sum of point
masses at the points of `F`, with the weights its own atoms.  So the constructed leaf is a
`fiberMeasure`, and its integrals are sums over the fiber.

This makes the leaf an explicit object rather than a limit: everything about it is determined by the
numbers `μ {ξ}`, `ξ ∈ F`.
-/

open scoped BigOperators
open MeasureTheory

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **A measure carried by a countable set is the weighted Dirac family of its own atoms.** -/
theorem measure_eq_fiberMeasure_of_carried (μ : Measure ℝ) [IsFiniteMeasure μ] {F : Set ℝ}
    (hF : F.Countable) (hFm : MeasurableSet F) (hcar : μ Fᶜ = 0) :
    μ = fiberMeasure (fun x => (μ {x}).toReal) F := by
  refine Measure.ext fun A hA => ?_
  have hdiff : μ (A \ F) = 0 :=
    le_antisymm (le_trans (measure_mono (Set.diff_subset_compl A F)) (le_of_eq hcar)) zero_le
  have hsplit : μ (A ∩ F) = μ A := by
    have := measure_inter_add_diff (μ := μ) A hFm
    rw [hdiff, add_zero] at this
    exact this
  have hAF : (A ∩ F).Countable := hF.mono Set.inter_subset_right
  have hleft : μ A = ∑' x : ℝ, (A ∩ F).indicator (fun y => μ {y}) x := by
    rw [← hsplit, measure_eq_tsum_singleton _ hAF]
    exact tsum_subtype (A ∩ F) fun y => μ {y}
  have hterm : ∀ p : ↥F, ENNReal.ofReal ((μ {(p : ℝ)}).toReal) * A.indicator 1 (p : ℝ)
      = μ {(p : ℝ)} * A.indicator 1 (p : ℝ) := by
    intro p
    rw [ENNReal.ofReal_toReal (measure_ne_top μ _)]
  have hright : fiberMeasure (fun x => (μ {x}).toReal) F A
      = ∑' x : ℝ, F.indicator (fun y => μ {y} * A.indicator 1 y) x := by
    rw [fiberMeasure_apply _ F hA, tsum_congr hterm]
    exact tsum_subtype F fun y => μ {y} * A.indicator 1 y
  rw [hleft, hright]
  refine tsum_congr fun x => ?_
  by_cases hxF : x ∈ F
  · by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem (Set.mem_inter hxA hxF), Set.indicator_of_mem hxF,
        Set.indicator_of_mem hxA, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem (fun hc => hxA hc.1), Set.indicator_of_mem hxF,
        Set.indicator_of_notMem hxA, mul_zero]
  · rw [Set.indicator_of_notMem (fun hc => hxF hc.2), Set.indicator_of_notMem hxF]

/-- **The leaf of a finite parameter is an explicit weighted Dirac family on its fiber.** -/
theorem exists_leaf_eq_fiberMeasure (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (tau : ℝ) :
    ∃ μ : ProbabilityMeasure ℝ,
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (μ : Measure ℝ) ∧
        (μ : Measure ℝ)
          = fiberMeasure (fun x => ((μ : Measure ℝ) {x}).toReal)
              ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau) := by
  obtain ⟨μ, hmom, hcar⟩ :=
    exists_leaf_finiteDenominatorFiber_of_moment_zero_eq_one h h0b h0 tau
  exact ⟨μ, hmom, measure_eq_fiberMeasure_of_carried _
    (countable_finiteDenominatorFiber h h0b tau)
    (isClosed_finiteDenominatorFiber h h0b tau).measurableSet hcar⟩

/-- **The leaf at infinity is an explicit weighted Dirac family on its fiber.** -/
theorem exists_leaf_infinity_eq_fiberMeasure (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    ∃ μ : ProbabilityMeasure ℝ,
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (μ : Measure ℝ) ∧
        (μ : Measure ℝ)
          = fiberMeasure (fun x => ((μ : Measure ℝ) {x}).toReal)
              (nevMatrixDataInf h h0b).infinityDenominatorFiber := by
  obtain ⟨μ, hmom, hcar⟩ := exists_leaf_infinityDenominatorFiber h h0b
  have hmom' : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (μ : Measure ℝ) := by
    intro k
    refine ⟨(hmom k).1, ?_⟩
    simpa [h0] using (hmom k).2
  exact ⟨μ, hmom', measure_eq_fiberMeasure_of_carried _
    (countable_infinityDenominatorFiber h h0b)
    (isClosed_infinityDenominatorFiber h h0b).measurableSet hcar⟩

end HTGeometry
