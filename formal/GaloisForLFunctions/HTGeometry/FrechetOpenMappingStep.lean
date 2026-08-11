import GaloisForLFunctions.HTGeometry.FrechetHalvingBasis

/-!
# The one-step approximation of the open mapping theorem

Two ingredients for the series argument.  A closure is contained in the set thickened by any
symmetric neighbourhood of the origin, and a point in the closure of an image can be approximated by
an image point with a prescribed error.

* `closure_subset_add` : `\overline S ⊆ S + V` for symmetric `V ∈ 𝓝 0`.
* `exists_approx_of_mem_closure_image` : **the one-step choice.**
-/

namespace GaloisForLFunctions

open Filter Set Pointwise Topology

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul 𝕜 F]

/-- **A closure is inside the set thickened by any symmetric neighbourhood of the origin.** -/
theorem closure_subset_add {S V : Set E} (hV : V ∈ 𝓝 (0 : E)) (hVsymm : -V = V) :
    closure S ⊆ S + V := by
  intro x hx
  have hnhd : (fun z : E => z - x) ⁻¹' V ∈ 𝓝 x := by
    have hc : ContinuousAt (fun z : E => z - x) x :=
      (continuous_id.sub continuous_const).continuousAt
    refine hc.preimage_mem_nhds ?_
    simpa using hV
  obtain ⟨w, hwV, hwS⟩ := mem_closure_iff_nhds.1 hx _ hnhd
  refine Set.mem_add.2 ⟨w, hwS, x - w, ?_, by abel⟩
  have hneg : x - w = -(w - x) := by abel
  rw [hneg, ← hVsymm]
  exact Set.neg_mem_neg.2 hwV

/-- **The one-step choice.**  If `y` lies in the closure of `f '' S` and `N` is a symmetric
neighbourhood of the origin, then `y` is an image point of `S` up to an error in `N`. -/
theorem exists_approx_of_mem_closure_image (f : E →ₗ[𝕜] F) {S : Set E} {N : Set F} {y : F}
    (hy : y ∈ closure (f '' S)) (hN : N ∈ 𝓝 (0 : F)) (hNsymm : -N = N) :
    ∃ x ∈ S, y - f x ∈ N := by
  have hnhd : (fun z : F => z - y) ⁻¹' N ∈ 𝓝 y := by
    have hc : ContinuousAt (fun z : F => z - y) y :=
      (continuous_id.sub continuous_const).continuousAt
    refine hc.preimage_mem_nhds ?_
    simpa using hN
  obtain ⟨w, hwN, hwS⟩ := mem_closure_iff_nhds.1 hy _ hnhd
  obtain ⟨x, hxS, rfl⟩ := hwS
  refine ⟨x, hxS, ?_⟩
  have hneg : y - f x = -(f x - y) := by abel
  rw [hneg, ← hNsymm]
  exact Set.neg_mem_neg.2 hwN

end GaloisForLFunctions
