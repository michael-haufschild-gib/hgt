import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# A continuous map vanishing on a set vanishes on the closed span

The kernel of a continuous linear map is a closed submodule, so it contains the closure of the span
of any set on which the map vanishes.  This is the step that converts a family of scalar
annihilation identities — one per index — into the vanishing of the functional on a whole closed
subspace.

* `HTGeometry.eq_zero_on_topologicalClosure_span`;
* `HTGeometry.eq_zero_of_topologicalClosure_span_eq_top`.
-/

namespace HTGeometry

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [T1Space F] [IsTopologicalAddGroup F]

omit [IsTopologicalAddGroup F] in
/-- **Vanishing propagates to the closed span.** -/
theorem eq_zero_on_topologicalClosure_span (L : E →L[𝕜] F) (S : Set E)
    (h : ∀ x ∈ S, L x = 0) :
    ∀ x ∈ (Submodule.span 𝕜 S).topologicalClosure, L x = 0 := by
  have hker : IsClosed ((LinearMap.ker (L : E →ₗ[𝕜] F) : Submodule 𝕜 E) : Set E) := by
    have hpre : IsClosed ((L : E → F) ⁻¹' {0}) :=
      (isClosed_singleton (x := (0 : F))).preimage L.continuous
    have hset : ((LinearMap.ker (L : E →ₗ[𝕜] F) : Submodule 𝕜 E) : Set E)
        = (L : E → F) ⁻¹' {0} := by
      ext x
      simp [LinearMap.mem_ker]
    rw [hset]
    exact hpre
  have hsub : Submodule.span 𝕜 S ≤ LinearMap.ker (L : E →ₗ[𝕜] F) :=
    Submodule.span_le.2 fun x hx => by simpa using h x hx
  have hclos : (Submodule.span 𝕜 S).topologicalClosure ≤ LinearMap.ker (L : E →ₗ[𝕜] F) :=
    Submodule.topologicalClosure_minimal _ hsub hker
  intro x hx
  simpa using hclos hx

omit [IsTopologicalAddGroup F] in
/-- **A functional vanishing on a set with dense span is zero.** -/
theorem eq_zero_of_topologicalClosure_span_eq_top (L : E →L[𝕜] F) (S : Set E)
    (h : ∀ x ∈ S, L x = 0) (hdense : (Submodule.span 𝕜 S).topologicalClosure = ⊤) :
    ∀ x : E, L x = 0 := by
  intro x
  refine eq_zero_on_topologicalClosure_span L S h x ?_
  rw [hdense]
  trivial

end HTGeometry
