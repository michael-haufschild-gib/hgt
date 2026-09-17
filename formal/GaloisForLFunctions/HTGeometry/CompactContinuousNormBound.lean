import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Compactness converts a continuous norm field into one nonnegative bound. -/

namespace GaloisForLFunctions.HTGeometry

theorem exists_compact_continuous_norm_bound
    {X E : Type*} [TopologicalSpace X] [SeminormedAddGroup E]
    {K : Set X} (hK : IsCompact K) (F : X → E) (hF : ContinuousOn F K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖F x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  exact (hC x hx).trans (le_max_left _ _)

end GaloisForLFunctions.HTGeometry
