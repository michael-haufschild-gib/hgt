import GaloisForLFunctions.HTGeometry.GlobalDisconnectedLocalSpectralCancellation

/-!
# Exact connected-cluster decomposition of local spectral branches

Every globally labelled simple spectral branch has an exact Boolean Möbius
packet expansion.  Spatially disconnected packet terms vanish as germs, while
every packet term is delayed to at least its packet cardinality along any
coupling ray.  Hence, near zero coupling, the full branch is exactly its
constant sector plus spatially indecomposable interaction packets.
-/

open Filter Topology Asymptotics

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]

/-- An interaction packet is spatially disconnected when its labels admit a
nontrivial disjoint partition whose two unions of site supports are disjoint. -/
def SpatiallyDisconnectedPacket
    (L : FiniteLocalInteractionFamily V E A)
    (packet : Finset E) : Prop :=
  ∃ left right : Finset E,
    Disjoint left right ∧ left.Nonempty ∧ right.Nonempty ∧
      left ∪ right = packet ∧
      Disjoint
        (L.packetSiteSupport left)
        (L.packetSiteSupport right)

/-- Irreducible Boolean response carried by one interaction packet. -/
def spectralPacketResponse
    (branch : (E → ℂ) → ℂ)
    (packet : Finset E) (z : E → ℂ) : ℂ :=
  finsetMobiusResponse packet
    (fun active =>
      branch (restrictInteractionPacket active z))

/-- Every spatially disconnected packet component of one global simple
spectral branch vanishes as a germ. -/
theorem globalBranch_spectralPacketResponse_germ_eq_zero_of_disconnected
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x : ∀ v, A v)
    (branch : (E → ℂ) → ℂ)
    (hbranch : AnalyticAt ℂ branch 0)
    (hbranch0 : branch 0 = onsiteProductEnergy onsite x)
    (hbranchRoot :
      ∀ᶠ coupling in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            L.globalInteraction coupling,
            branch coupling) = 0)
    (packet : Finset E)
    (hpacket : SpatiallyDisconnectedPacket L packet) :
    spectralPacketResponse branch packet =ᶠ[𝓝 0]
      (fun _ : E → ℂ => (0 : ℂ)) := by
  obtain ⟨left, right, hlabel, hleft, hright,
      hunion, hsite⟩ := hpacket
  have hzero :=
    L.globalBranch_disconnectedPacket_mobius_germ_eq_zero
      onsite hinj left right hlabel hleft hright hsite x
      branch hbranch hbranch0 hbranchRoot
  unfold spectralPacketResponse
  rw [← hunion]
  exact hzero

/-- **Packet-depth law.**  The irreducible response of every interaction
packet is `O(|g|^|packet|)` along every scalar coupling ray. -/
theorem spectralPacketResponse_couplingRay_isBigO
    (branch : (E → ℂ) → ℂ)
    (hbranch : AnalyticAt ℂ branch 0)
    (z : E → ℂ) (packet : Finset E) :
    (fun g : ℂ =>
      spectralPacketResponse branch packet (g • z))
      =O[𝓝 0]
    fun g : ℂ => ‖g‖ ^ packet.card := by
  have h :=
    AnalyticAt.posetMobiusProbe_couplingRay_isBigO
      hbranch z packet
  apply h.congr_left
  intro g
  unfold spectralPacketResponse
  rw [finsetMobiusResponse_eq_posetMobiusProbe]
  congr 2
  funext active
  apply congrArg branch
  funext e
  simp [restrictInteractionPacket]

/-- **Exact packet reconstruction.**  At every coupling vector, the full
spectral branch is the sum of all irreducible packet responses. -/
theorem sum_spectralPacketResponse_eq_branch
    (branch : (E → ℂ) → ℂ) (z : E → ℂ) :
    ∑ packet : Finset E,
        spectralPacketResponse branch packet z =
      branch z := by
  let response : Finset E → ℂ :=
    fun active =>
      branch (restrictInteractionPacket active z)
  have h := sum_finsetMobiusResponse_eq_full response
  have hfull : response Finset.univ = branch z := by
    unfold response
    congr 1
    funext e
    simp [restrictInteractionPacket]
  simpa [spectralPacketResponse, response, hfull] using h

/-- Finite family consisting of the constant packet and all spatially
indecomposable interaction packets. -/
noncomputable def spatiallyIndecomposablePackets
    (L : FiniteLocalInteractionFamily V E A) :
    Finset (Finset E) := by
  classical
  exact (Finset.univ : Finset (Finset E)).filter
    (fun packet =>
      ¬SpatiallyDisconnectedPacket L packet)

/-- **Exact local spectral connected-cluster law.**  Near zero coupling,
every analytic branch through a simple product level is exactly the sum of
its spatially indecomposable packet responses.  All disconnected packets
cancel identically; every surviving packet of `r` generators has onset at
least order `r`. -/
theorem globalBranch_eq_sum_spatiallyIndecomposablePacketResponses_germ
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x : ∀ v, A v)
    (branch : (E → ℂ) → ℂ)
    (hbranch : AnalyticAt ℂ branch 0)
    (hbranch0 : branch 0 = onsiteProductEnergy onsite x)
    (hbranchRoot :
      ∀ᶠ coupling in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            L.globalInteraction coupling,
            branch coupling) = 0) :
    branch =ᶠ[𝓝 0]
      (fun z =>
        ∑ packet ∈ spatiallyIndecomposablePackets L,
          spectralPacketResponse branch packet z) := by
  classical
  let disconnectedPackets :=
    (Finset.univ : Finset (Finset E)).filter
      (SpatiallyDisconnectedPacket L)
  have hzero :
      ∀ packet ∈ disconnectedPackets,
        spectralPacketResponse branch packet =ᶠ[𝓝 0]
          (fun _ : E → ℂ => (0 : ℂ)) := by
    intro packet hpacket
    exact
      L.globalBranch_spectralPacketResponse_germ_eq_zero_of_disconnected
        onsite hinj x branch hbranch hbranch0 hbranchRoot packet
        (Finset.mem_filter.mp hpacket).2
  have hall :
      ∀ᶠ z : E → ℂ in 𝓝 0,
        ∀ packet ∈ disconnectedPackets,
          spectralPacketResponse branch packet z = 0 := by
    rw [Finset.eventually_all]
    intro packet hpacket
    exact hzero packet hpacket
  filter_upwards [hall] with z hz
  rw [← sum_spectralPacketResponse_eq_branch branch z]
  symm
  unfold spatiallyIndecomposablePackets
  apply Finset.sum_subset
  · intro packet hpacket
    simp
  · intro packet hpacket hnot
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and] at hnot
    have hdisc :
        SpatiallyDisconnectedPacket L packet := by
      by_contra hn
      exact hnot hn
    exact hz packet (by
      simp [disconnectedPackets, hdisc])

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
