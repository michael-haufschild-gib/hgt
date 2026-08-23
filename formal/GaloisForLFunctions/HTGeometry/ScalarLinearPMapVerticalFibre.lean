import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Analysis.Complex.Basic

/-!
# Scalar partial-linear-map vertical fibres

The vertical fibre of the closed graph relation of a scalar-valued partial linear map is a complex
subspace of `ℂ`. Hence it is either zero or the full scalar line, and it is zero exactly when the
partial map is closable. This is the reusable one-dimensional graph dichotomy behind singular
scalar-incidence no-go results.
-/

open Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [AddCommGroup E] [Module ℂ E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℂ E]

/-- The linear embedding of the scalar vertical axis into `E × ℂ`. -/
def scalarVerticalEmbedding : ℂ →ₗ[ℂ] (E × ℂ) where
  toFun := fun c => (0, c)
  map_add' := by intro x y; simp
  map_smul' := by intro x y; simp

/-- Vertical fibre of the topological closure of a scalar-valued partial linear map's graph. -/
def scalarLinearPMapVerticalFibre (T : E →ₗ.[ℂ] ℂ) : Submodule ℂ ℂ :=
  T.graph.topologicalClosure.comap scalarVerticalEmbedding

/-- A scalar-valued partial linear map is closable exactly when its closed-graph vertical fibre is
zero. -/
theorem scalarLinearPMap_isClosable_iff_verticalFibre_eq_bot (T : E →ₗ.[ℂ] ℂ) :
    T.IsClosable ↔ scalarLinearPMapVerticalFibre T = ⊥ := by
  constructor
  · intro hT
    unfold scalarLinearPMapVerticalFibre
    rw [hT.graph_closure_eq_closure_graph]
    apply le_antisymm
    · intro c hc
      change (0, c) ∈ T.closure.graph at hc
      have hc0 : c = 0 := T.closure.graph_fst_eq_zero_snd hc rfl
      change c = 0
      exact hc0
    · exact bot_le
  · intro hbot
    refine ⟨T.graph.topologicalClosure.toLinearPMap, ?_⟩
    rw [Submodule.toLinearPMap_graph_eq]
    intro c hc hc0
    have hvert : c.2 ∈ scalarLinearPMapVerticalFibre T := by
      change (0, c.2) ∈ T.graph.topologicalClosure
      have heq : c = (0, c.2) := Prod.ext hc0 rfl
      rw [heq] at hc
      exact hc
    rw [hbot] at hvert
    simpa using hvert

/-- Every scalar closed-graph vertical fibre is either zero or the whole complex line. -/
theorem scalarLinearPMap_verticalFibre_eq_bot_or_top (T : E →ₗ.[ℂ] ℂ) :
    scalarLinearPMapVerticalFibre T = ⊥ ∨ scalarLinearPMapVerticalFibre T = ⊤ := by
  by_cases hbot : scalarLinearPMapVerticalFibre T = ⊥
  · exact Or.inl hbot
  · right
    rw [eq_top_iff]
    intro c _
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hsmul := (scalarLinearPMapVerticalFibre T).smul_mem (c / v) hv
    simpa [smul_eq_mul, div_mul_cancel₀ c hv0] using hsmul

/-- Nonclosability is equivalent to saturation of the scalar vertical fibre. -/
theorem scalarLinearPMap_verticalFibre_eq_top_iff_not_isClosable (T : E →ₗ.[ℂ] ℂ) :
    scalarLinearPMapVerticalFibre T = ⊤ ↔ ¬ T.IsClosable := by
  rw [scalarLinearPMap_isClosable_iff_verticalFibre_eq_bot]
  constructor
  · intro htop hbot
    rw [hbot] at htop
    exact bot_ne_top htop
  · intro hnot
    rcases scalarLinearPMap_verticalFibre_eq_bot_or_top T with hbot | htop
    · exact absurd hbot hnot
    · exact htop

end GaloisForLFunctions.HTGeometry
