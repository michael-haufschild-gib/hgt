import GaloisForLFunctions.HTGeometry.InteractionPacketRelabelling
import GaloisForLFunctions.HTGeometry.DisconnectedLocalSpectralGermCancellation

/-!
# Disconnected cancellation on arbitrary interaction packets

The split-sector spectral theorem is transported back to the ordinary subtype
of any disjoint label union.  Thus disconnected cancellation is an intrinsic
property of an arbitrary active packet, not an artifact of coproduct labels.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]

/-- **Arbitrary-packet disconnected spectral cancellation.**  If a nonempty
active label packet splits into two nonempty, label-disjoint parts with
disjoint site supports, every analytic eigenvalue branch through a simple
product level has zero irreducible full-packet response as a germ. -/
theorem disconnectedPacketBranch_mobius_germ_eq_zero
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (left right : Finset E)
    (hlabel : Disjoint left right)
    (hleft : left.Nonempty) (hright : right.Nonempty)
    (hsite :
      Disjoint (L.packetSiteSupport left) (L.packetSiteSupport right))
    (x : ∀ v, A v)
    (branch : ({e : E // e ∈ left ∪ right} → ℂ) → ℂ)
    (hbranch : AnalyticAt ℂ branch 0)
    (hbranch0 : branch 0 = onsiteProductEnergy onsite x)
    (hbranchRoot :
      ∀ᶠ coupling in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            (fun e : {e : E // e ∈ left ∪ right} =>
              L.globalInteraction e.1)
            coupling,
            branch coupling) = 0) :
    (fun z =>
      finsetMobiusResponse
        (Finset.univ : Finset {e : E // e ∈ left ∪ right})
        (fun active =>
          branch (restrictInteractionPacket active z)))
      =ᶠ[𝓝 0]
        (fun _ : ({e : E // e ∈ left ∪ right} → ℂ) =>
          (0 : ℂ)) := by
  let P := Sum {e : E // e ∈ left} {e : E // e ∈ right}
  let U := {e : E // e ∈ left ∪ right}
  let q : P ≃ U := splitInteractionLabelEquiv left right hlabel
  let branchP : (P → ℂ) → ℂ :=
    fun z => branch (relabelCoupling q z)
  have hbranchP : AnalyticAt ℂ branchP 0 := by
    exact hbranch.comp_of_eq' (relabelCoupling_analyticAt q) rfl
  have hbranchP0 :
      branchP 0 = onsiteProductEnergy onsite x := by
    simpa [branchP] using hbranch0
  have hbranchPRoot :
      ∀ᶠ coupling in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            (L.splitPacketGlobalInteraction left right)
            coupling,
            branchP coupling) = 0 := by
    filter_upwards [
      (relabelCoupling_tendsto_zero q).eventually hbranchRoot]
      with coupling hroot
    rw [← L.affineMatrixFamily_relabel_splitPacket
      onsite left right hlabel coupling]
    exact hroot
  have hgermP :=
    L.disconnectedLocalBranch_crossPacket_germ_eq_zero
      onsite hinj left right hleft hright hsite x branchP
      hbranchP hbranchP0 hbranchPRoot
  have hpull :=
    hgermP.comp_tendsto (relabelCoupling_tendsto_zero q.symm)
  filter_upwards [hpull] with z hz
  let fullP : Finset P :=
    (Finset.univ : Finset {e : E // e ∈ left}).map
        (sumInlEmbedding {e : E // e ∈ left}
          {e : E // e ∈ right}) ∪
      (Finset.univ : Finset {e : E // e ∈ right}).map
        (sumInrEmbedding {e : E // e ∈ left}
          {e : E // e ∈ right})
  let responseP : Finset P → ℂ :=
    fun active =>
      branchP
        (restrictInteractionPacket active
          (relabelCoupling q.symm z))
  have hsource :
      finsetMobiusResponse fullP responseP = 0 := by
    change finsetMobiusResponse fullP responseP = 0 at hz
    exact hz
  have hrename := finsetMobiusResponse_equiv q fullP responseP
  rw [hsource] at hrename
  have hfullP : fullP = (Finset.univ : Finset P) := by
    ext p
    simp only [Finset.mem_univ, iff_true]
    cases p with
    | inl e =>
        exact Finset.mem_union_left _
          (Finset.mem_map.mpr ⟨e, Finset.mem_univ _, rfl⟩)
    | inr e =>
        exact Finset.mem_union_right _
          (Finset.mem_map.mpr ⟨e, Finset.mem_univ _, rfl⟩)
  have hfull :
      q.finsetCongr fullP = (Finset.univ : Finset U) := by
    rw [hfullP]
    ext u
    simp
  rw [hfull] at hrename
  rw [← hrename]
  apply congrArg
    (fun r => finsetMobiusResponse (Finset.univ : Finset U) r)
  funext active
  unfold responseP branchP
  apply congrArg branch
  rw [relabelCoupling_restrictInteractionPacket]
  have hpacket :
      q.finsetCongr (q.symm.finsetCongr active) = active := by
    ext u
    simp
  have hcoupling :
      relabelCoupling q (relabelCoupling q.symm z) = z :=
    relabelCoupling_symm_relabelCoupling q.symm z
  rw [hpacket, hcoupling]

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
