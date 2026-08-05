import GaloisForLFunctions.HTGeometry.LocalSpectralConnectedClusterDecomposition

/-!
# Spatially disconnected packets exist

A packet is spatially disconnected when it splits into two nonempty halves whose site supports do
not meet.  The condition is exactly that a splitting exists, so exhibiting one discharges it; and
a two-edge family whose edges sit on different sites has a disconnected packet, which shows the
cluster decomposition is not a statement about an empty class.
-/

namespace GaloisForLFunctions.HTGeometry

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
  {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

/-- **A splitting with disjoint site supports disconnects the packet it unites.** -/
theorem spatiallyDisconnectedPacket_of_disjoint_supports
    (L : FiniteLocalInteractionFamily V E A) {left right : Finset E}
    (hdisj : Disjoint left right) (hl : left.Nonempty) (hr : right.Nonempty)
    (hsupp : Disjoint (L.packetSiteSupport left) (L.packetSiteSupport right)) :
    L.SpatiallyDisconnectedPacket (left ∪ right) :=
  ⟨left, right, hdisj, hl, hr, rfl, hsupp⟩

/-- Two edges on their own separate sites. -/
def twoSiteInteractionFamily :
    FiniteLocalInteractionFamily Bool Bool (fun _ => Bool) where
  support := fun e => {e}
  interaction := fun _ => 1

/-- **The two-edge family has a spatially disconnected packet.** -/
theorem spatiallyDisconnectedPacket_twoSite :
    twoSiteInteractionFamily.SpatiallyDisconnectedPacket (Finset.univ : Finset Bool) := by
  have hunion : ({false} : Finset Bool) ∪ {true} = Finset.univ := by
    ext b
    cases b <;> simp
  rw [← hunion]
  refine spatiallyDisconnectedPacket_of_disjoint_supports twoSiteInteractionFamily ?_
    ⟨false, Finset.mem_singleton_self _⟩ ⟨true, Finset.mem_singleton_self _⟩ ?_
  · simp
  · simp [FiniteLocalInteractionFamily.packetSiteSupport, twoSiteInteractionFamily]

end GaloisForLFunctions.HTGeometry
