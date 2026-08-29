import GaloisForLFunctions.HTGeometry.LatticeSubsetMinimum

/-!
# Lattice-subset minima after a linear change of frame

A positive definite form is measured after an invertible linear change of coordinates.  This file
shows that any nonempty subset of a discrete lattice still attains a minimum for the transported
norm.  Compactness comes from pulling a closed ball back through the continuous linear equivalence.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric

/-- A nonempty subset of a discrete lattice attains minimum norm after any continuous real-linear
equivalence. -/
theorem exists_minimal_image_norm_mem_of_nonempty_subset
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
    (L : Submodule ℤ E) [DiscreteTopology L]
    (S : Set E) (hS : S.Nonempty) (hSL : S ⊆ L)
    (e : E ≃L[ℝ] F) :
    ∃ v ∈ S, ∀ w ∈ S, ‖e v‖ ≤ ‖e w‖ := by
  rcases hS with ⟨w₀, hw₀S⟩
  let B : Set E := {x | ‖e x‖ ≤ ‖e w₀‖}
  have hBcompact : IsCompact B := by
    have hB : B = e.symm '' Metric.closedBall (0 : F) ‖e w₀‖ := by
      ext x
      constructor
      · intro hx
        refine ⟨e x, ?_, by simp⟩
        simpa [B, Metric.mem_closedBall] using hx
      · rintro ⟨y, hy, rfl⟩
        simpa [B, Metric.mem_closedBall] using hy
    rw [hB]
    exact (isCompact_closedBall (0 : F) ‖e w₀‖).image e.symm.continuous
  let T : Set E := S ∩ B
  have hTfinite : T.Finite := by
    apply (finite_lattice_inter_of_bounded L hBcompact.isBounded).subset
    intro x hx
    exact ⟨hx.2, hSL hx.1⟩
  have hw₀T : w₀ ∈ T := by
    exact ⟨hw₀S, by simp [B]⟩
  have hTnonempty : hTfinite.toFinset.Nonempty := by
    exact ⟨w₀, by simpa using hw₀T⟩
  rcases Finset.exists_min_image hTfinite.toFinset (fun x ↦ ‖e x‖) hTnonempty with
    ⟨v, hvT, hvmin⟩
  have hvT' : v ∈ T := by simpa using hvT
  refine ⟨v, hvT'.1, ?_⟩
  intro w hwS
  by_cases hwB : w ∈ B
  · apply hvmin
    simp [T, hwS, hwB]
  · have hw₀lt : ‖e w₀‖ < ‖e w‖ := by
      simpa [B, not_le] using hwB
    exact (hvmin w₀ (by simpa using hw₀T)).trans hw₀lt.le

end GaloisForLFunctions.HTGeometry
