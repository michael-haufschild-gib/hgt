import GaloisForLFunctions.HTGeometry.LatticeMinimalVectors

/-!
# Minimum norm on a subset of a discrete lattice

Primitive vectors over a Dedekind domain do not form a submodule.  The usual shortest-vector theorem
for a discrete submodule therefore does not apply directly.  Properness makes every bounded lattice
slice finite, which is enough to minimize the norm on any nonempty subset of the lattice.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric

/-- Every nonempty subset of a discrete lattice in a proper normed group contains a point of minimum
norm. -/
theorem exists_minimal_norm_mem_of_nonempty_subset
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L]
    (S : Set E) (hS : S.Nonempty) (hSL : S ⊆ L) :
    ∃ v ∈ S, ∀ w ∈ S, ‖v‖ ≤ ‖w‖ := by
  rcases hS with ⟨w₀, hw₀S⟩
  let T : Set E := S ∩ closedBall 0 ‖w₀‖
  have hTfinite : T.Finite := by
    apply (finite_lattice_inter_of_bounded L isBounded_closedBall).subset
    intro x hx
    exact ⟨hx.2, hSL hx.1⟩
  have hw₀T : w₀ ∈ T := by
    exact ⟨hw₀S, by simp⟩
  have hTnonempty : hTfinite.toFinset.Nonempty := by
    exact ⟨w₀, by simpa using hw₀T⟩
  rcases Finset.exists_min_image hTfinite.toFinset norm hTnonempty with
    ⟨v, hvT, hvmin⟩
  have hvT' : v ∈ T := by simpa using hvT
  refine ⟨v, hvT'.1, ?_⟩
  intro w hwS
  by_cases hwball : w ∈ closedBall (0 : E) ‖w₀‖
  · apply hvmin
    simp [T, hwS, hwball]
  · have hw₀lt : ‖w₀‖ < ‖w‖ := by
      simpa [mem_closedBall, not_le] using hwball
    exact (hvmin w₀ (by simpa using hw₀T)).trans hw₀lt.le

end GaloisForLFunctions.HTGeometry
