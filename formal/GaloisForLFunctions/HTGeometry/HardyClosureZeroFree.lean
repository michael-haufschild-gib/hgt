import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Closed-span zero obstruction for Hardy and Nyman--Beurling criteria

The 2026 Hardy-space refinement of the Baez--Duarte criterion
(`arXiv:2606.16097`) uses one elementary functional-analytic mechanism.  Point evaluation in the
relevant Hardy space is continuous.  If every approximating generator vanishes at a candidate
zeta zero while the target does not, then the target cannot lie in their closed linear span.

This module proves that mechanism for an arbitrary normed space and arbitrary continuous linear
functional.  It is the exact non-numerical core shared by Hardy, Nyman--Beurling, and damped
Colombeau--Beurling closure criteria.  Instantiating it with the paper's concrete half-plane Hardy
space still requires the half-plane `H^2` carrier, its bounded point evaluations, and the concrete
zeta generators; those are the current source-realization wall.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

variable {K H I : Type*} [NormedField K] [NormedAddCommGroup H] [NormedSpace K H]

/-- A continuous detector which kills every generator also kills their closed linear span. -/
theorem continuousLinearMap_eq_zero_on_closedSpan
    (L : H →L[K] K) (G : I → H)
    (hG : ∀ i, L (G i) = 0) :
    (Submodule.span K (Set.range G)).topologicalClosure ≤ L.ker := by
  apply Submodule.topologicalClosure_minimal
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hG i
  · exact ContinuousLinearMap.isClosed_ker L

/-- If a continuous evaluation kills all approximants but not the target, the target is not in
their closed span.  This is the direct closure obstruction used at a hypothetical zeta zero. -/
theorem not_mem_closedSpan_of_continuous_evaluation
    (L : H →L[K] K) (E : H) (G : I → H)
    (hG : ∀ i, L (G i) = 0) (hE : L E ≠ 0) :
    E ∉ (Submodule.span K (Set.range G)).topologicalClosure := by
  intro hmem
  exact hE (continuousLinearMap_eq_zero_on_closedSpan L G hG hmem)

/-- Closed-span membership and a nonzero target evaluation force at least one generator to be
visible at that evaluation.  In a Hardy application this rules out a common zero of all zeta
generators. -/
theorem exists_generator_evaluation_ne_zero_of_mem_closedSpan
    (L : H →L[K] K) (E : H) (G : I → H)
    (hmem : E ∈ (Submodule.span K (Set.range G)).topologicalClosure)
    (hE : L E ≠ 0) :
    ∃ i, L (G i) ≠ 0 := by
  by_contra hnone
  push Not at hnone
  exact (not_mem_closedSpan_of_continuous_evaluation L E G hnone hE) hmem

end GaloisForLFunctions.HTGeometry
