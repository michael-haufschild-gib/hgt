import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.LinearIsometry

noncomputable section

/-!
# Extending a linear isometry to the completion

A linear isometry into a complete space extends to the completion of its domain, and the extension
is again a linear isometry.  Additivity, homogeneity and the norm identity all transfer from the
dense image by continuity.  If the original map already had dense range, the extension is onto — its
range is complete, hence closed, and dense.
-/

open UniformSpace Topology

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem completion_extension_coe (L : E →ₗᵢ[𝕜] F) (a : E) :
    Completion.extension (L : E → F) (a : Completion E) = L a :=
  Completion.extension_coe L.isometry.uniformContinuous a

theorem continuous_completion_extension (L : E →ₗᵢ[𝕜] F) :
    Continuous (Completion.extension (L : E → F)) :=
  Completion.continuous_extension

/-- The extension of a linear isometry to the completion of its domain. -/
def completionExtendₗ (L : E →ₗᵢ[𝕜] F) : Completion E →ₗ[𝕜] F where
  toFun := Completion.extension (L : E → F)
  map_add' := by
    intro x y
    refine Completion.induction_on₂ x y ?_ ?_
    · refine isClosed_eq ?_ ?_
      · exact (continuous_completion_extension L).comp continuous_add
      · exact ((continuous_completion_extension L).comp continuous_fst).add
          ((continuous_completion_extension L).comp continuous_snd)
    · intro a b
      rw [← Completion.coe_add, completion_extension_coe, completion_extension_coe,
        completion_extension_coe, map_add]
  map_smul' := by
    intro c x
    refine Completion.induction_on x ?_ ?_
    · refine isClosed_eq ?_ ?_
      · exact (continuous_completion_extension L).comp (continuous_const_smul c)
      · exact (continuous_const_smul c).comp (continuous_completion_extension L)
    · intro a
      rw [← Completion.coe_smul, completion_extension_coe, completion_extension_coe,
        map_smul]
      rfl

/-- The extension is again a linear isometry. -/
def completionExtendₗᵢ (L : E →ₗᵢ[𝕜] F) : Completion E →ₗᵢ[𝕜] F where
  toLinearMap := completionExtendₗ L
  norm_map' := by
    intro x
    refine Completion.induction_on x ?_ ?_
    · refine isClosed_eq ?_ ?_
      · exact continuous_norm.comp (continuous_completion_extension L)
      · exact continuous_norm
    · intro a
      show ‖Completion.extension (L : E → F) (a : Completion E)‖ = ‖(a : Completion E)‖
      rw [completion_extension_coe, L.norm_map, Completion.norm_coe]

@[simp] theorem completionExtendₗᵢ_coe (L : E →ₗᵢ[𝕜] F) (a : E) :
    completionExtendₗᵢ L (a : Completion E) = L a :=
  completion_extension_coe L a

theorem denseRange_completionExtendₗᵢ_of_denseRange (L : E →ₗᵢ[𝕜] F)
    (h : DenseRange (L : E → F)) : Function.Surjective (completionExtendₗᵢ L) := by
  have hclosed : IsClosed (Set.range (completionExtendₗᵢ L)) :=
    (completionExtendₗᵢ L).isometry.isClosedEmbedding.isClosed_range
  have hdense : Dense (Set.range (completionExtendₗᵢ L)) := by
    refine h.mono ?_
    intro y hy
    obtain ⟨a, ha⟩ := hy
    exact ⟨(a : Completion E), by rw [completionExtendₗᵢ_coe]; exact ha⟩
  intro y
  have hrange : Set.range (completionExtendₗᵢ L) = Set.univ := by
    rw [← hclosed.closure_eq, hdense.closure_eq]
  have hy : y ∈ Set.range (completionExtendₗᵢ L) := by
    rw [hrange]
    exact Set.mem_univ y
  exact hy

end GaloisForLFunctions.HTGeometry
