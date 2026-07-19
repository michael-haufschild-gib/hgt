import GaloisForLFunctions.HTGeometry.InfinityLeaf
import GaloisForLFunctions.HTGeometry.NevFiberCountable
import GaloisForLFunctions.HTGeometry.CountableWeightedDirac

/-!
# The Christoffel weights on a fiber sum to at least the total mass

The constructed leaf is a probability measure carried by a countable fiber, so its mass is the sum of
its atoms; and every atom of a representing measure is at most the Christoffel limit there.  Hence
the Christoffel limits on the fiber sum to at least `1`.

This reduces the remaining core to the reverse inequality: once the sum is known to be at most `1`,
equality is forced termwise and every atom of the leaf equals `λ (ξ)`.
-/

open scoped BigOperators
open MeasureTheory

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- A measure of a countable set is the sum of its atoms. -/
theorem measure_eq_tsum_singleton (μ : Measure ℝ) {S : Set ℝ} (hS : S.Countable) :
    μ S = ∑' ξ : ↥S, μ {(ξ : ℝ)} := by
  have hdisj : S.PairwiseDisjoint (fun b : ℝ => ({b} : Set ℝ)) := by
    intro a _ b _ hab
    simpa [Function.onFun] using hab
  have hmeas : ∀ b ∈ S, MeasurableSet ({b} : Set ℝ) := fun b _ => measurableSet_singleton b
  have hU : (⋃ b ∈ S, ({b} : Set ℝ)) = S := by
    ext x
    simp
  conv_lhs => rw [← hU]
  exact measure_biUnion hS hdisj hmeas

/-- An atom of a representing measure, in `ENNReal` form. -/
theorem measure_singleton_le_ofReal_christoffelLimit (h : PositiveMomentForm s)
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hmom : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ) (x : ℝ) :
    μ {x} ≤ ENNReal.ofReal (christoffelLimit s x) := by
  have hle : μ.real {x} ≤ christoffelLimit s x :=
    measureReal_singleton_le_christoffelLimit_of_hasMoments h hmom x
  have htop : μ {x} ≠ ⊤ := measure_ne_top μ _
  calc μ {x} = ENNReal.ofReal ((μ {x}).toReal) := (ENNReal.ofReal_toReal htop).symm
    _ ≤ ENNReal.ofReal (christoffelLimit s x) := ENNReal.ofReal_le_ofReal hle

/-- **The Christoffel weights on a finite-parameter fiber sum to at least one.** -/
theorem one_le_tsum_christoffelLimit_finiteFiber (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) (tau : ℝ) :
    1 ≤ ∑' ξ : ↥((nevMatrixDataInf h h0b).finiteDenominatorFiber tau),
        ENNReal.ofReal (christoffelLimit s (ξ : ℝ)) := by
  obtain ⟨μ, hmom, hcar⟩ :=
    exists_leaf_finiteDenominatorFiber_of_moment_zero_eq_one h h0b h0 tau
  have hFc : ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau).Countable :=
    countable_finiteDenominatorFiber h h0b tau
  have hFm : MeasurableSet ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau) :=
    (isClosed_finiteDenominatorFiber h h0b tau).measurableSet
  have hprob : IsProbabilityMeasure (μ : Measure ℝ) := inferInstance
  have hfull : (μ : Measure ℝ) ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau) = 1 := by
    have h2 := measure_add_measure_compl (μ := (μ : Measure ℝ)) hFm
    rw [hcar, add_zero, measure_univ] at h2
    exact h2
  rw [measure_eq_tsum_singleton _ hFc] at hfull
  rw [← hfull]
  exact ENNReal.tsum_le_tsum fun ξ =>
    measure_singleton_le_ofReal_christoffelLimit h hmom (ξ : ℝ)

/-- **The Christoffel weights on the infinity fiber sum to at least one.** -/
theorem one_le_tsum_christoffelLimit_infinityFiber (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    1 ≤ ∑' ξ : ↥(nevMatrixDataInf h h0b).infinityDenominatorFiber,
        ENNReal.ofReal (christoffelLimit s (ξ : ℝ)) := by
  obtain ⟨μ, hmom, hcar⟩ := exists_leaf_infinityDenominatorFiber h h0b
  have hmom' : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (μ : Measure ℝ) := by
    intro k
    refine ⟨(hmom k).1, ?_⟩
    simpa [h0] using (hmom k).2
  have hFc : (nevMatrixDataInf h h0b).infinityDenominatorFiber.Countable :=
    countable_infinityDenominatorFiber h h0b
  have hFm : MeasurableSet (nevMatrixDataInf h h0b).infinityDenominatorFiber :=
    (isClosed_infinityDenominatorFiber h h0b).measurableSet
  have hprob : IsProbabilityMeasure (μ : Measure ℝ) := inferInstance
  have hfull : (μ : Measure ℝ) (nevMatrixDataInf h h0b).infinityDenominatorFiber = 1 := by
    have h2 := measure_add_measure_compl (μ := (μ : Measure ℝ)) hFm
    rw [hcar, add_zero, measure_univ] at h2
    exact h2
  rw [measure_eq_tsum_singleton _ hFc] at hfull
  rw [← hfull]
  exact ENNReal.tsum_le_tsum fun ξ =>
    measure_singleton_le_ofReal_christoffelLimit h hmom' (ξ : ℝ)

/-- **Equality of the weight sum forces every atom to be the Christoffel limit.**  With the reverse
inequality in hand, the leaf's atoms are exactly `λ (ξ)`. -/
theorem measure_singleton_eq_of_tsum_le (h : PositiveMomentForm s) {μ : Measure ℝ}
    [IsFiniteMeasure μ] (hmom : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ)
    {F : Set ℝ} (hFc : F.Countable) (hFm : MeasurableSet F) (hcar : μ Fᶜ = 0)
    (hmass : μ Set.univ = 1)
    (hsum : ∑' ξ : ↥F, ENNReal.ofReal (christoffelLimit s (ξ : ℝ)) ≤ 1) (ξ : ↥F) :
    μ {(ξ : ℝ)} = ENNReal.ofReal (christoffelLimit s (ξ : ℝ)) := by
  have hfull : μ F = 1 := by
    have h2 := measure_add_measure_compl (μ := μ) hFm
    rw [hcar, add_zero, hmass] at h2
    exact h2
  rw [measure_eq_tsum_singleton _ hFc] at hfull
  have hterm : ∀ η : ↥F, μ {(η : ℝ)} ≤ ENNReal.ofReal (christoffelLimit s (η : ℝ)) :=
    fun η => measure_singleton_le_ofReal_christoffelLimit h hmom (η : ℝ)
  have heq : ∑' η : ↥F, μ {(η : ℝ)}
      = ∑' η : ↥F, ENNReal.ofReal (christoffelLimit s (η : ℝ)) :=
    le_antisymm (ENNReal.tsum_le_tsum hterm) (by rw [hfull]; exact hsum)
  by_contra hne
  have hlt : μ {(ξ : ℝ)} < ENNReal.ofReal (christoffelLimit s (ξ : ℝ)) :=
    lt_of_le_of_ne (hterm ξ) hne
  have hstrict : ∑' η : ↥F, μ {(η : ℝ)}
      < ∑' η : ↥F, ENNReal.ofReal (christoffelLimit s (η : ℝ)) := by
    refine ENNReal.tsum_lt_tsum (i := ξ) ?_ hterm hlt
    rw [hfull]
    exact ENNReal.one_ne_top
  exact absurd heq (ne_of_lt hstrict)

end HTGeometry
