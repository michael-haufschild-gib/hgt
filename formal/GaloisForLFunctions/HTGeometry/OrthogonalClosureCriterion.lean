import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Identifying the closure of a subspace by an orthogonality criterion

A subspace of a Hilbert space contained in a closed subspace has that closed subspace as its
closure exactly when no nonzero vector of the closed subspace is orthogonal to it.  The proof is
the orthogonal decomposition along the closure: the component orthogonal to the closure still lies
in the closed subspace, hence vanishes.

* `submodule_topologicalClosure_eq_of_orthogonal_inf_eq_bot`
-/

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **A closed subspace whose intersection with the orthogonal complement of a subspace is trivial
is that subspace's closure.** -/
theorem submodule_topologicalClosure_eq_of_orthogonal_inf_eq_bot
    {K V : Submodule 𝕜 E} (hKV : K ≤ V) (hVc : IsClosed (V : Set E))
    (hbot : Kᗮ ⊓ V = ⊥) : K.topologicalClosure = V := by
  refine le_antisymm (K.topologicalClosure_minimal hKV hVc) fun a ha => ?_
  have hsup : K.topologicalClosure ⊔ K.topologicalClosureᗮ = ⊤ :=
    Submodule.sup_orthogonal_of_hasOrthogonalProjection
  have hmem : a ∈ K.topologicalClosure ⊔ K.topologicalClosureᗮ := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hmem
  have hpV : p ∈ V := K.topologicalClosure_minimal hKV hVc hp
  have hqV : q ∈ V := by
    have hqa : q = a - p := by
      rw [← hpq, add_sub_cancel_left]
    rw [hqa]
    exact V.sub_mem ha hpV
  have hqK : q ∈ Kᗮ := Submodule.orthogonal_le K.le_topologicalClosure hq
  have hq0 : q = 0 := by
    have hmem' : q ∈ Kᗮ ⊓ V := ⟨hqK, hqV⟩
    rwa [hbot, Submodule.mem_bot] at hmem'
  rw [← hpq, hq0, add_zero]
  exact hp

open scoped InnerProductSpace in
/-- **Orthogonality to a spanning set is orthogonality to the span.** -/
theorem mem_span_orthogonal {S : Set E} {x : E}
    (h : ∀ u ∈ S, (inner 𝕜 u x : 𝕜) = 0) : x ∈ (Submodule.span 𝕜 S)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => rw [inner_zero_left]
  | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
  | smul c y _ hy => rw [inner_smul_left, hy, mul_zero]


end GaloisForLFunctions.HTGeometry
