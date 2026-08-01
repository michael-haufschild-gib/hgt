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

/-- **Two limits along a cluster filter agree.**  If `x` is a cluster point of the family and a
continuous functional of the family converges along the index filter, the functional's value at `x`
is that limit.  Stating it this way lets a *single* cluster point serve every functional, which is
what a representation theorem needs. -/
theorem eq_of_clusterPt_of_tendsto {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {l : Filter ι} {P : ι → X} {x : X} (hcl : ClusterPt x (map P l))
    {Φ : X → Y} (hΦ : Continuous Φ) {y : Y} (hy : Tendsto (fun i => Φ (P i)) l (𝓝 y)) :
    Φ x = y := by
  haveI : (𝓝 x ⊓ map P l).NeBot := hcl
  exact tendsto_nhds_unique ((hΦ.continuousAt (x := x)).mono_left inf_le_left)
    ((tendsto_map' hy).mono_left inf_le_right)

/-- A family eventually inside a compact set has a cluster point there. -/
theorem exists_clusterPt_of_isCompact {X ι : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsCompact S) {l : Filter ι} [Filter.NeBot l] {P : ι → X}
    (hP : ∀ᶠ i in l, P i ∈ S) : ∃ x ∈ S, ClusterPt x (map P l) :=
  hS.exists_clusterPt (le_principal_iff.mpr (mem_map.mpr hP))

/-- **The limit is attained at a cluster point.**  If a family lies in a compact set and a
continuous functional of it converges along the index filter, then the limit is that functional
evaluated at some point of the set. -/
theorem exists_mem_of_tendsto_of_isCompact {X Y ι : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {S : Set X} (hS : IsCompact S) {l : Filter ι} [Filter.NeBot l]
    {P : ι → X} (hP : ∀ᶠ i in l, P i ∈ S) {Φ : X → Y} (hΦ : Continuous Φ) {y : Y}
    (hy : Tendsto (fun i => Φ (P i)) l (𝓝 y)) :
    ∃ x ∈ S, Φ x = y := by
  obtain ⟨x, hxS, hcl⟩ := exists_clusterPt_of_isCompact hS hP
  exact ⟨x, hxS, eq_of_clusterPt_of_tendsto hcl hΦ hy⟩

/-- The same conclusion when the family is confined to the closure of a set whose closure is
compact — the form Prokhorov's theorem delivers. -/
theorem exists_mem_closure_of_tendsto_of_isCompact {X Y ι : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {S : Set X} (hS : IsCompact (closure S))
    {l : Filter ι} [Filter.NeBot l] {P : ι → X} (hP : ∀ᶠ i in l, P i ∈ S) {Φ : X → Y}
    (hΦ : Continuous Φ) {y : Y}
    (hy : Tendsto (fun i => Φ (P i)) l (𝓝 y)) :
    ∃ x ∈ closure S, Φ x = y :=
  exists_mem_of_tendsto_of_isCompact hS (hP.mono fun _ hi => subset_closure hi) hΦ hy

/-- A family eventually inside a set with compact closure has a cluster point in that closure. -/
theorem exists_clusterPt_closure_of_isCompact {X ι : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsCompact (closure S)) {l : Filter ι} [Filter.NeBot l] {P : ι → X}
    (hP : ∀ᶠ i in l, P i ∈ S) : ∃ x ∈ closure S, ClusterPt x (map P l) :=
  exists_clusterPt_of_isCompact hS (hP.mono fun _ hi => subset_closure hi)

end GaloisForLFunctions.HTGeometry
