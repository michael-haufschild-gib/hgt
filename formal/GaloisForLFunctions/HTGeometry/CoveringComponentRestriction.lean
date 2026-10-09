import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Restricting coverings to source components

Over a locally connected base, restricting a covering to a clopen part of its
source again gives a covering. On a connected evenly covered neighborhood,
each sheet lies wholly inside or outside that clopen part. The proof retains
exactly the sheets inside, including the possibility of no retained sheets.
-/

open Topology Set Function

namespace GaloisForLFunctions.HTGeometry

/-- Restricting a covering to a clopen part of its source preserves the covering
property over a locally connected base, including empty fibers. -/
theorem isCoveringMap_restrict_clopen [TopologicalSpace E] [TopologicalSpace B]
    [LocallyConnectedSpace B] {p : E → B} (hp : IsCoveringMap p)
    {C : Set E} (hC : IsClopen C) : IsCoveringMap (fun e : C => p e) := by
  classical
  intro b
  obtain ⟨hI, U, hbU, hU, _, H, hH⟩ := hp b
  letI := hI
  let W := connectedComponentIn U b
  have hbW : b ∈ W := mem_connectedComponentIn hbU
  have hWo : IsOpen W := hU.connectedComponentIn
  have hWc : IsConnected W := isConnected_connectedComponentIn_iff.mpr hbU
  have hWU : W ⊆ U := connectedComponentIn_subset _ _
  letI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hWc
  let σ : (p ⁻¹' {b}) → W → E := fun i w => H.symm (⟨w, hWU w.property⟩, i)
  have hσcont : ∀ i, Continuous (σ i) := by
    intro i
    exact continuous_subtype_val.comp (H.symm.continuous.comp (by fun_prop))
  have hσproj : ∀ i w, p (σ i w) = (w : B) := by
    intro i w
    have h := hH (H.symm (⟨w, hWU w.property⟩, i))
    simpa only [Homeomorph.apply_symm_apply] using h.symm
  have hσmem : ∀ i w, σ i w ∈ C ↔ σ i ⟨b, hbW⟩ ∈ C := by
    intro i w
    have hc : IsClopen ((σ i) ⁻¹' C) := hC.preimage (hσcont i)
    constructor
    · intro hw
      exact Set.eq_univ_iff_forall.mp (hc.eq_univ ⟨w, hw⟩) ⟨b, hbW⟩
    · intro hb
      exact Set.eq_univ_iff_forall.mp (hc.eq_univ ⟨⟨b, hbW⟩, hb⟩) w
  let J := {i : p ⁻¹' {b} // σ i ⟨b, hbW⟩ ∈ C}
  let q : C → B := fun e => p e
  have hq : Continuous q := hp.continuous.comp continuous_subtype_val
  have hback : ∀ e : q ⁻¹' W,
      σ (H ⟨e.val.val, hWU e.property⟩).2 ⟨q e.val, e.property⟩ = e.val.val := by
    intro e
    have hx := hH ⟨e.val.val, hWU e.property⟩
    have hpair : (⟨q e.val, hWU e.property⟩, (H ⟨e.val.val, hWU e.property⟩).2) =
        H ⟨e.val.val, hWU e.property⟩ := Prod.ext (Subtype.ext hx.symm) rfl
    change (H.symm _).val = _
    rw [hpair, H.symm_apply_apply]
  let F : (q ⁻¹' W) → W × J := fun e =>
    (⟨q e.val, e.property⟩, ⟨(H ⟨e.val.val, hWU e.property⟩).2,
      (hσmem _ _).mp (by rw [hback]; exact e.val.property)⟩)
  let G : W × J → (q ⁻¹' W) := fun wi =>
    ⟨⟨σ wi.2.val wi.1, (hσmem _ _).mpr wi.2.property⟩,
      by change p (σ wi.2.val wi.1) ∈ W; rw [hσproj]; exact wi.1.property⟩
  have hGF : ∀ e, G (F e) = e := by
    intro e
    apply Subtype.ext
    apply Subtype.ext
    exact hback e
  have hFG : ∀ wi, F (G wi) = wi := by
    intro wi
    apply Prod.ext
    · apply Subtype.ext
      exact hσproj _ _
    · apply Subtype.ext
      change (H ⟨σ wi.2.val wi.1, _⟩).2 = wi.2.val
      have hx : (⟨σ wi.2.val wi.1, hWU (G wi).property⟩ : p ⁻¹' U) =
          H.symm (⟨wi.1, hWU wi.1.property⟩, wi.2.val) := rfl
      rw [hx, H.apply_symm_apply]
  have hFc : Continuous F := by
    apply Continuous.prodMk
    · exact (hq.comp continuous_subtype_val).subtype_mk _
    · apply Continuous.subtype_mk
      exact continuous_snd.comp (H.continuous.comp
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))
  have hGc : Continuous G := by
    dsimp [G, σ, J]
    fun_prop
  have hc : IsEvenlyCovered q b J :=
    ⟨inferInstance, W, hbW, hWo, hWo.preimage hq,
      ⟨⟨F, G, hGF, hFG⟩, hFc, hGc⟩, fun _ => rfl⟩
  exact hc.to_isEvenlyCovered_preimage

/-- Each connected component of the source of a covering is itself a covering
when source and base are locally connected. -/
theorem isCoveringMap_connectedComponent [TopologicalSpace E] [TopologicalSpace B]
    [LocallyConnectedSpace E] [LocallyConnectedSpace B]
    {p : E → B} (hp : IsCoveringMap p) (e : E) :
    IsCoveringMap (fun x : connectedComponent e => p x) :=
  isCoveringMap_restrict_clopen hp isClopen_connectedComponent

/-- Restrict to an open base set and then to any source component. -/
theorem isCoveringMap_open_preimage_component [TopologicalSpace E] [TopologicalSpace B]
    [LocallyConnectedSpace E] [LocallyConnectedSpace B]
    {p : E → B} (hp : IsCoveringMap p) {U : Set B} (hU : IsOpen U)
    (e : p ⁻¹' U) :
    IsCoveringMap (fun x : connectedComponent e => U.restrictPreimage p x) := by
  letI : LocallyConnectedSpace U := hU.locallyConnectedSpace
  letI : LocallyConnectedSpace (p ⁻¹' U) :=
    (hU.preimage hp.continuous).locallyConnectedSpace
  exact isCoveringMap_connectedComponent
    (hp.isCoveringMapOn.mono (subset_univ U)).isCoveringMap_restrictPreimage e

end GaloisForLFunctions.HTGeometry
