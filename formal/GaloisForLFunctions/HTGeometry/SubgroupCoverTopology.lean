import GaloisForLFunctions.HTGeometry.SubgroupCover
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Bases

/-!
# Topology of subgroup covers

The quotient construction gives Hausdorffness over a Hausdorff base and
second countability from a second countable universal source. Open pieces
then have countably many connected components, controlling the cap index.
-/

open Topology Set Function

namespace GaloisForLFunctions.HTGeometry

variable {E B G : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [Group G] [MulAction G E] {p : E → B}

/-- Subgroup covers over a Hausdorff, locally connected base are Hausdorff. -/
theorem t2Space_subgroupCover [T2Space B] [LocallyConnectedSpace B]
    (hp : IsQuotientCoveringMap p G) (H : Subgroup G) :
    T2Space (SubgroupCover (E := E) H) := by
  let q := subgroupCoverProjection hp H
  have hq : Continuous q := (isCoveringMap_subgroupCoverProjection hp H).continuous
  refine ⟨fun x y hxy => ?_⟩
  by_cases h : q x = q y
  · exact isSeparatedMap_subgroupCoverProjection hp H x y h hxy
  · obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation h
    exact ⟨q ⁻¹' U, q ⁻¹' V, hU.preimage hq, hV.preimage hq, hxU, hyV,
      hUV.preimage q⟩

/-- The quotient-cover construction preserves second countability. -/
theorem secondCountableTopology_subgroupCover [SecondCountableTopology E]
    (hp : IsQuotientCoveringMap p G) (H : Subgroup G) :
    SecondCountableTopology (SubgroupCover (E := E) H) :=
  isQuotientMap_quotient_mk'.secondCountableTopology
    (isQuotientCoveringMap_subgroupQuotient hp H).isCoveringMap.isOpenMap

/-- Open pieces of a locally connected, second countable space have at most
countably many connected components. -/
theorem countable_connectedComponents_open [LocallyConnectedSpace E]
    [SecondCountableTopology E] {U : Set E} (hU : IsOpen U) :
    Countable (ConnectedComponents U) := by
  letI := hU.locallyConnectedSpace
  exact TopologicalSpace.separableSpace_iff_countable.mp
    ConnectedComponents.isQuotientMap_coe.separableSpace

end GaloisForLFunctions.HTGeometry
