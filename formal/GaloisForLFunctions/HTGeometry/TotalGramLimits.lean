import GaloisForLFunctions.HTGeometry.TotalGramNegativeDefinite

/-!
# The total scaled Gram converges to the coefficient diagonal

The deviation of the total Gram from the coefficient diagonal is the sum of the atomic deviation and
the measure entry, so the two limits add.  No squeeze is needed: both summands converge, and the
limit of a sum is the sum of the limits.

With that the chamber lower bound is unconditional in the four limits, and the scaled Gram is
negative definite at all small heights whenever every coefficient is negative.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology MeasureTheory Matrix

noncomputable section

/-- **The total diagonal converges to the coefficient.** -/
theorem tendsto_totalGram_diagonal_sub {d : ℕ} (ν : Measure ℝ) (a c : Fin d → ℝ)
    (ha : Function.Injective a) (l : Fin d)
    (hmeas : Tendsto (fun y : ℝ => measureGram ν a y l l) (𝓝[≠] 0) (𝓝 0)) :
    Tendsto (fun y : ℝ => totalGram ν a c y l l - ((c l : ℝ) : ℂ)) (𝓝[≠] 0) (𝓝 0) := by
  have h := (tendsto_atomicGram_diagonal_sub a c ha l).add hmeas
  rw [add_zero] at h
  refine h.congr fun y => ?_
  rw [totalGram_apply]
  ring

/-- **The total off-diagonal converges to zero.** -/
theorem tendsto_totalGram_offdiag {d : ℕ} (ν : Measure ℝ) (a c : Fin d → ℝ)
    (ha : Function.Injective a) {l m : Fin d} (hlm : l ≠ m)
    (hmeas : Tendsto (fun y : ℝ => measureGram ν a y l m) (𝓝[≠] 0) (𝓝 0)) :
    Tendsto (fun y : ℝ => totalGram ν a c y l m) (𝓝[≠] 0) (𝓝 0) := by
  have h := (tendsto_atomicGram_offdiag a c ha hlm).add hmeas
  rw [add_zero] at h
  exact h

/-- **The chamber lower bound.**  With the measure part vanishing at every node and every coefficient
negative, the total scaled Gram is negative definite at all small heights. -/
theorem eventually_negDef_totalGram_of_measure_vanishing {d : ℕ}
    (ν : Measure ℝ) (a c : Fin d → ℝ) (ha : Function.Injective a)
    {δ : ℝ} (hδ : 0 < δ) (hc : ∀ j, c j ≤ -δ)
    (hmeasDiag : ∀ l : Fin d,
      Tendsto (fun y : ℝ => measureGram ν a y l l) (𝓝[≠] 0) (𝓝 0))
    (hmeasOff : ∀ l m : Fin d, l ≠ m →
      Tendsto (fun y : ℝ => measureGram ν a y l m) (𝓝[≠] 0) (𝓝 0)) :
    ∀ᶠ y : ℝ in 𝓝[≠] 0, ∀ x : Fin d → ℂ, x ≠ 0 →
      (star x ⬝ᵥ (totalGram ν a c y).mulVec x).re < 0 :=
  eventually_negDef_totalGram ν a c hδ hc
    (fun l => tendsto_totalGram_diagonal_sub ν a c ha l (hmeasDiag l))
    (fun l m hlm => tendsto_totalGram_offdiag ν a c ha hlm (hmeasOff l m hlm))

end

end GaloisForLFunctions.HTGeometry
