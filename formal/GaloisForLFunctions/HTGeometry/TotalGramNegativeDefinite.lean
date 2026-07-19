import GaloisForLFunctions.HTGeometry.MeasureGramLimits

/-!
# The scaled Gram is eventually negative definite

Assembling the chamber lower bound.  The diagonal entries of the total scaled Gram converge to the
atom coefficients and the off-diagonal entries to zero, so on a finite index the whole matrix
converges entrywise to the coefficient diagonal.

When every coefficient is negative that diagonal is negative definite with a margin, so the Gram is
negative definite for all small heights.  Its negative index is then at least the number of atoms,
which is the lower bound of the chamber law.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology MeasureTheory Matrix

noncomputable section

/-- **The total scaled Gram is eventually negative definite.**  Entrywise convergence to a negative
coefficient diagonal makes the Gram negative definite at all small heights. -/
theorem eventually_negDef_totalGram {d : ℕ} (ν : Measure ℝ) (a c : Fin d → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hc : ∀ j, c j ≤ -δ)
    (hdiag : ∀ l : Fin d,
      Tendsto (fun y : ℝ => totalGram ν a c y l l - ((c l : ℝ) : ℂ)) (𝓝[≠] 0) (𝓝 0))
    (hoff : ∀ l m : Fin d, l ≠ m →
      Tendsto (fun y : ℝ => totalGram ν a c y l m) (𝓝[≠] 0) (𝓝 0)) :
    ∀ᶠ y : ℝ in 𝓝[≠] 0, ∀ x : Fin d → ℂ, x ≠ 0 →
      (star x ⬝ᵥ (totalGram ν a c y).mulVec x).re < 0 := by
  classical
  refine eventually_negDef_of_entrywise_tendsto_diagonal
    (fun y => totalGram ν a c y) c hδ hc ?_
  intro ε hε
  rw [Filter.eventually_all]
  intro j
  rw [Filter.eventually_all]
  intro k
  by_cases hjk : j = k
  · subst hjk
    have h := (NormedAddGroup.tendsto_nhds_zero.1 (hdiag j)) ε hε
    filter_upwards [h] with y hy
    rw [Matrix.diagonal_apply_eq]
    exact hy.le
  · have h := (NormedAddGroup.tendsto_nhds_zero.1 (hoff j k hjk)) ε hε
    filter_upwards [h] with y hy
    rw [Matrix.diagonal_apply_ne _ hjk, sub_zero]
    exact hy.le

end

end GaloisForLFunctions.HTGeometry
