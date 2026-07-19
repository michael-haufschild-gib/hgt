import GaloisForLFunctions.HTGeometry.GaussTightness

/-!
# The Gauss measure attains the Christoffel value

`ChristoffelPointMass` bounds the atom of any representing measure at a point by the Christoffel
function there.  At finite level that bound is sharp, and visibly so: the Gauss measure places mass
exactly `λₙ(ξ)` at each of its nodes, by construction.

This is the finite-level form of attainment.  It does not conflict with the bound, because the Gauss
measure reproduces only the moments up to order `2n+1` and so is not a representing measure for the
full sequence.
-/

open scoped BigOperators
open MeasureTheory

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The Gauss measure charges each node by its Christoffel weight.** -/
theorem gaussMeasure_singleton (n : ℕ) {xi : ℝ} (hxi : xi ∈ gaussNodes s n) :
    gaussMeasure s n {xi} = ENNReal.ofReal (christoffel s n xi) := by
  classical
  rw [gaussMeasure, finsetWeightedDirac_apply _ _ (measurableSet_singleton xi),
    Finset.sum_eq_single xi]
  · rw [Set.indicator_of_mem (Set.mem_singleton xi)]
    simp
  · intro y _ hne
    rw [Set.indicator_of_notMem (by simpa using hne)]
    simp
  · intro hnot
    exact absurd hxi hnot

/-- The same as a real-valued mass. -/
theorem gaussMeasure_real_singleton (h : PositiveMomentForm s) (n : ℕ) {xi : ℝ}
    (hxi : xi ∈ gaussNodes s n) :
    (gaussMeasure s n).real {xi} = christoffel s n xi := by
  rw [Measure.real, gaussMeasure_singleton n hxi,
    ENNReal.toReal_ofReal (christoffel_pos h n xi).le]

/-- **The finite-level bound is sharp.**  The Christoffel value at a node is exactly the mass the
Gauss measure of that level places there, so no smaller bound than `λₙ` is available. -/
theorem exists_measure_real_singleton_eq_christoffel (h : PositiveMomentForm s) (n : ℕ) {xi : ℝ}
    (hxi : xi ∈ gaussNodes s n) :
    ∃ nu : Measure ℝ, nu.real {xi} = christoffel s n xi ∧
      ∀ k : ℕ, k ≤ 2 * n + 1 → ∫ x, x ^ k ∂nu = s k :=
  ⟨gaussMeasure s n, gaussMeasure_real_singleton h n hxi,
    fun k hk => gaussMeasure_moment h n k hk⟩

end HTGeometry
