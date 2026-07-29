import GaloisForLFunctions.HTGeometry.LocalSpectralConnectedClusterDecomposition
import GaloisForLFunctions.HTGeometry.LocalSpectralPacketLocality
import GaloisForLFunctions.HTGeometry.LocalSpectralJetCausality

/-!
# Spatial locality of irreducible spectral packet responses

For a nonempty interaction packet, the constant spectator-energy difference
between two product configurations is killed by Boolean Möbius probing.  The
irreducible packet response therefore depends, as a germ, only on the sites
touched by that packet.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]

/-- Express a full-space packet response on the subtype of its packet. -/
theorem spectralPacketResponse_eq_subtypeResponse
    (branch : (E → ℂ) → ℂ)
    (packet : Finset E) (z : E → ℂ) :
    spectralPacketResponse branch packet z =
      finsetMobiusResponse
        (Finset.univ : Finset {e : E // e ∈ packet})
        (fun active =>
          branch (extendCouplingFromPacket packet
            (restrictInteractionPacket active
              (restrictCouplingToPacket packet z)))) := by
  unfold spectralPacketResponse
  rw [← finsetMobiusResponse_subtype_univ packet]
  apply congrArg
    (fun r => finsetMobiusResponse
      (Finset.univ : Finset {e : E // e ∈ packet}) r)
  funext active
  apply congrArg branch
  funext e
  by_cases he : e ∈ packet
  · simp [extendCouplingFromPacket, restrictCouplingToPacket,
      restrictInteractionPacket, he]
  · have hnot :
        e ∉ active.map (Function.Embedding.subtype _) := by
      intro hmem
      obtain ⟨a, ha, hae⟩ := Finset.mem_map.mp hmem
      exact he (hae ▸ a.2)
    simp [extendCouplingFromPacket,
      restrictInteractionPacket, he, hnot]

/-- **Packet-response spatial locality.**  If two product configurations
agree on every site touched by a nonempty interaction packet, their
irreducible packet responses are the same germ at zero coupling. -/
theorem productEigenvalueBranch_spectralPacketResponse_germ_eq_of_eqOn
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (packet : Finset E) (hpacket : packet.Nonempty)
    {x y : ∀ v, A v}
    (hxy :
      ∀ v ∈ L.packetSiteSupport packet, x v = y v) :
    spectralPacketResponse
        (L.productEigenvalueBranch onsite hinj x) packet
      =ᶠ[𝓝 0]
    spectralPacketResponse
        (L.productEigenvalueBranch onsite hinj y) packet := by
  let branchX :=
    L.productEigenvalueBranch onsite hinj x
  let branchY :=
    L.productEigenvalueBranch onsite hinj y
  have hx := L.productEigenvalueBranch_spec onsite hinj x
  have hy := L.productEigenvalueBranch_spec onsite hinj y
  have hdiff :=
    L.restrictedBranches_difference_germ_eq_spectatorDifference
      onsite hinj branchX branchY hx.1 hy.1 hx.2.1 hy.2.1
      hx.2.2 hy.2.2 packet hxy
  let U := {e : E // e ∈ packet}
  let D :=
    outsideOnsiteEnergy onsite (L.packetSiteSupport packet)
        (restrictOutsideConfiguration
          (L.packetSiteSupport packet) x) -
      outsideOnsiteEnergy onsite (L.packetSiteSupport packet)
        (restrictOutsideConfiguration
          (L.packetSiteSupport packet) y)
  have hactive :
      ∀ active : Finset U,
        (fun z : U → ℂ =>
          branchX (extendCouplingFromPacket packet
            (restrictInteractionPacket active z)) -
          branchY (extendCouplingFromPacket packet
            (restrictInteractionPacket active z)))
          =ᶠ[𝓝 0]
        (fun _ : U → ℂ => D) := by
    intro active
    have htendsto :
        Tendsto (restrictInteractionPacket active)
          (𝓝 (0 : U → ℂ)) (𝓝 0) := by
      have hc :=
        (restrictInteractionPacket_analyticAt active).continuousAt
      have hzero :
          restrictInteractionPacket active
            (0 : U → ℂ) = 0 := by
        funext e
        simp [restrictInteractionPacket]
      change Tendsto (restrictInteractionPacket active) (𝓝 0)
        (𝓝 (restrictInteractionPacket active 0)) at hc
      rw [hzero] at hc
      exact hc
    simpa [branchX, branchY, D] using
      hdiff.comp_tendsto htendsto
  have hall :
      ∀ᶠ z : U → ℂ in 𝓝 0,
        ∀ active ∈ Finset.Iic (Finset.univ : Finset U),
          branchX (extendCouplingFromPacket packet
            (restrictInteractionPacket active z)) -
          branchY (extendCouplingFromPacket packet
            (restrictInteractionPacket active z)) = D := by
    rw [Finset.eventually_all]
    intro active hactiveMem
    exact hactive active
  have hsubtype :
      (fun z : U → ℂ =>
        finsetMobiusResponse Finset.univ
          (fun active =>
            branchX (extendCouplingFromPacket packet
              (restrictInteractionPacket active z))))
        =ᶠ[𝓝 0]
      (fun z : U → ℂ =>
        finsetMobiusResponse Finset.univ
          (fun active =>
            branchY (extendCouplingFromPacket packet
              (restrictInteractionPacket active z)))) := by
    filter_upwards [hall] with z hz
    let responseX : Finset U → ℂ :=
      fun active =>
        branchX (extendCouplingFromPacket packet
          (restrictInteractionPacket active z))
    let responseY : Finset U → ℂ :=
      fun active =>
        branchY (extendCouplingFromPacket packet
          (restrictInteractionPacket active z))
    have hresp :
        responseX = responseY + fun _ => D := by
      funext active
      have hd :=
        hz active
          (Finset.mem_Iic.mpr
            (Finset.subset_univ active))
      dsimp [responseX, responseY]
      exact eq_add_of_sub_eq' hd
    change finsetMobiusResponse Finset.univ responseX =
      finsetMobiusResponse Finset.univ responseY
    rw [hresp, finsetMobiusResponse_add]
    have huniv :
        (Finset.univ : Finset U).Nonempty := by
      obtain ⟨e, he⟩ := hpacket
      exact ⟨⟨e, he⟩, Finset.mem_univ _⟩
    obtain ⟨e, he⟩ := huniv
    have hconst :
        finsetMobiusResponse (Finset.univ : Finset U)
          (fun _ => D) = 0 := by
      apply finsetMobiusResponse_eq_zero_of_insert_invariant he
      intro active
      rfl
    rw [hconst, add_zero]
  have hpull :=
    hsubtype.comp_tendsto
      (restrictCouplingToPacket_tendsto_zero packet)
  filter_upwards [hpull] with z hz
  rw [spectralPacketResponse_eq_subtypeResponse,
    spectralPacketResponse_eq_subtypeResponse]
  exact hz

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
