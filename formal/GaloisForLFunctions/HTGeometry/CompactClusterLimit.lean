import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# Limits at cluster points of a compact family

A family confined to a compact set need not converge, but it has a cluster point, and that is
enough whenever the conclusion is about a continuous functional of the family: the functional's
limit along the index filter is its value at the cluster point.

This replaces the usual "extract a convergent subsequence" step and needs no metrizability,
countability, or sequences — only that the ambient space be compact where the family lives and that
the target be Hausdorff.  The mechanism is that the cluster filter refines both the neighbourhood
filter of the cluster point and the image of the index filter, so the two limits computed along it
must agree.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-- **The limit is attained at a cluster point.**  If a family lies in a compact set and a
continuous functional of it converges along the index filter, then the limit is that functional
evaluated at some point of the set. -/
theorem exists_mem_of_tendsto_of_isCompact {X Y ι : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {S : Set X} (hS : IsCompact S) {l : Filter ι} [Filter.NeBot l]
    {P : ι → X} (hP : ∀ i, P i ∈ S) {Φ : X → Y} (hΦ : Continuous Φ) {y : Y}
    (hy : Tendsto (fun i => Φ (P i)) l (𝓝 y)) :
    ∃ x ∈ S, Φ x = y := by
  have hle : map P l ≤ 𝓟 S :=
    le_principal_iff.mpr (mem_map.mpr (Eventually.of_forall hP))
  obtain ⟨x, hxS, hcl⟩ := hS.exists_clusterPt hle
  refine ⟨x, hxS, ?_⟩
  haveI : (𝓝 x ⊓ map P l).NeBot := hcl
  have h₁ : Tendsto Φ (𝓝 x ⊓ map P l) (𝓝 (Φ x)) :=
    (hΦ.continuousAt (x := x)).mono_left inf_le_left
  have h₂ : Tendsto Φ (𝓝 x ⊓ map P l) (𝓝 y) :=
    (tendsto_map' hy).mono_left inf_le_right
  exact tendsto_nhds_unique h₁ h₂

/-- The same conclusion when the family is confined to the closure of a set whose closure is
compact — the form Prokhorov's theorem delivers. -/
theorem exists_mem_closure_of_tendsto_of_isCompact {X Y ι : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {S : Set X} (hS : IsCompact (closure S))
    {l : Filter ι} [Filter.NeBot l] {P : ι → X} (hP : ∀ i, P i ∈ S) {Φ : X → Y}
    (hΦ : Continuous Φ) {y : Y}
    (hy : Tendsto (fun i => Φ (P i)) l (𝓝 y)) :
    ∃ x ∈ closure S, Φ x = y :=
  exists_mem_of_tendsto_of_isCompact hS (fun i => subset_closure (hP i)) hΦ hy

end GaloisForLFunctions.HTGeometry
