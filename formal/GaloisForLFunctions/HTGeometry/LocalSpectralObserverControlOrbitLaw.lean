import GaloisForLFunctions.HTGeometry.HermitianLocalSpectralObserverLaw
import GaloisForLFunctions.HTGeometry.InteractionPacketCoordinateInvariance

/-!
# Connected reconstruction of every observer control orbit

An observer does not receive one spectral response but a Boolean control
orbit: the response obtained after every subset of independently switchable
interaction channels is activated.  Boolean Möbius inversion gives its
canonical irreducible packet coordinates.

For local spectral families the reconstruction is much smaller than the
formal Boolean expansion.  The empty interaction sector is zero for every
linear spectral observer, and locality annihilates every spatially
disconnected packet as a germ.  Thus every restricted experiment is exactly
reconstructed, near zero coupling, from its nonempty spatially
indecomposable subpackets.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]

/-- **Restricted Boolean reconstruction.**  For every activated control
subset, the response of an arbitrary function is exactly the sum of the
irreducible packet responses supported inside that subset. -/
theorem sum_spectralPacketResponse_powerset_eq_restrict
    (branch : (E → ℂ) → ℂ) (active : Finset E) (z : E → ℂ) :
    ∑ packet ∈ active.powerset,
        spectralPacketResponse branch packet z =
      branch (restrictInteractionPacket active z) := by
  have hall :=
    sum_spectralPacketResponse_eq_branch branch
      (restrictInteractionPacket active z)
  rw [← hall]
  change
    (∑ packet ∈ active.powerset,
      spectralPacketResponse branch packet z) =
    ∑ packet : Finset E,
      spectralPacketResponse branch packet
        (restrictInteractionPacket active z)
  rw [show (∑ packet : Finset E,
      spectralPacketResponse branch packet
        (restrictInteractionPacket active z)) =
      ∑ packet : Finset E,
        if packet ⊆ active then
          spectralPacketResponse branch packet z else 0 by
    apply Finset.sum_congr rfl
    intro packet hpacket
    exact spectralPacketResponse_restrictInteractionPacket
      branch packet active z]
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext packet
  simp

/-- Nonempty spatially indecomposable subpackets of one activated control
set. -/
noncomputable def observerConnectedSubpackets
    (L : FiniteLocalInteractionFamily V E A)
    (active : Finset E) : Finset (Finset E) := by
  classical
  exact active.powerset.filter
    (fun packet => packet.Nonempty ∧
      ¬SpatiallyDisconnectedPacket L packet)

/-- **Observer-time connected reconstruction law.**  For every continuous
linear spectral observer and every activated subset of controls, the complete
restricted response germ is exactly the sum of its nonempty spatially
indecomposable packet sectors. -/
theorem linearSpectralObserverRestrictedResponse_eq_sum_connectedSubpackets_germ
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (observer : ((∀ v, A v) → ℂ) →L[ℂ] ℂ)
    (active : Finset E) :
    (fun z =>
      L.linearSpectralObserverResponse onsite hinj observer
        (restrictInteractionPacket active z)) =ᶠ[𝓝 0]
      (fun z =>
        ∑ packet ∈ observerConnectedSubpackets L active,
          L.linearSpectralObserverPacketResponse onsite hinj
            observer packet z) := by
  classical
  have hraw (z : E → ℂ) :=
    sum_spectralPacketResponse_powerset_eq_restrict
      (L.linearSpectralObserverResponse onsite hinj observer) active z
  have hempty :
      L.linearSpectralObserverPacketResponse onsite hinj observer ∅ =
        (fun _ : E → ℂ => 0) := by
    funext z
    unfold linearSpectralObserverPacketResponse
    rw [spectralPacketResponse_empty]
    unfold linearSpectralObserverResponse
    have hvector :
        L.productSpectralInteractionShiftVector onsite hinj 0 = 0 := by
      funext config
      unfold productSpectralInteractionShiftVector
      unfold productSpectralInteractionShift
      rw [(L.productEigenvalueBranch_spec onsite hinj config).2.1]
      simp
    rw [hvector, map_zero]
  let omitted :=
    active.powerset \ observerConnectedSubpackets L active
  have homitted : ∀ packet ∈ omitted,
      L.linearSpectralObserverPacketResponse onsite hinj observer packet
        =ᶠ[𝓝 0] (fun _ : E → ℂ => 0) := by
    intro packet hpacket
    have hmem := Finset.mem_sdiff.mp hpacket
    have hnot := hmem.2
    rw [observerConnectedSubpackets, Finset.mem_filter] at hnot
    simp only [hmem.1, true_and, not_and_or] at hnot
    rcases hnot with hemptyPacket | hdisconnected
    · have hp : packet = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hemptyPacket
      simpa [hp] using Filter.Eventually.of_forall
        (fun z => congrFun hempty z)
    · exact
        L.linearSpectralObserverPacketResponse_germ_eq_zero_of_disconnected
          onsite hinj observer packet (not_not.mp hdisconnected)
  have hall : ∀ᶠ z : E → ℂ in 𝓝 0,
      ∀ packet ∈ omitted,
        L.linearSpectralObserverPacketResponse onsite hinj
          observer packet z = 0 := by
    rw [Finset.eventually_all]
    intro packet hpacket
    exact homitted packet hpacket
  filter_upwards [hall] with z hz
  rw [← hraw z]
  symm
  apply Finset.sum_subset
  · intro packet hpacket
    exact (Finset.mem_filter.mp hpacket).1
  · intro packet hpacket hnot
    exact hz packet (Finset.mem_sdiff.mpr ⟨hpacket, hnot⟩)

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
