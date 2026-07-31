import GaloisForLFunctions.HTGeometry.ObserverSteinerNumberLaw

/-!
# When a spanning packet exists

The sharp form of the observer Steiner law is conditional on the existence of a connected packet
spanning the queried sites, and that existence was never produced.

A singleton packet is never spatially disconnected — a one-element set is not the disjoint union of
two nonempty sets — so a single interaction touching every queried site is already a spanning
packet.  The onset order is then at most one, and the Steiner number is pinned from above with no
further hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)] [∀ v, Nonempty (A v)]

omit [Fintype E] [∀ v, Nonempty (A v)] in
/-- A one-interaction packet is never spatially disconnected. -/
theorem not_spatiallyDisconnectedPacket_singleton
    (L : FiniteLocalInteractionFamily V E A) (e : E) :
    ¬ SpatiallyDisconnectedPacket L {e} := by
  rintro ⟨left, right, hdisj, ⟨a, ha⟩, ⟨b, hb⟩, hunion, -⟩
  have hamem : a ∈ ({e} : Finset E) := by
    rw [← hunion]
    exact Finset.mem_union_left _ ha
  have hbmem : b ∈ ({e} : Finset E) := by
    rw [← hunion]
    exact Finset.mem_union_right _ hb
  have hae : a = e := Finset.mem_singleton.mp hamem
  have hbe : b = e := Finset.mem_singleton.mp hbmem
  have haright : a ∈ right := by
    rw [hae, ← hbe]
    exact hb
  exact (Finset.disjoint_left.mp hdisj ha) haright

omit [Fintype E] [∀ v, Nonempty (A v)] in
/-- **One interaction can already span.**  If a single interaction touches every queried site, its
singleton packet is an observer-spanning packet. -/
theorem observerSpanningPacket_singleton
    (L : FiniteLocalInteractionFamily V E A) {sites : Finset V} {e : E}
    (h : sites ⊆ L.support e) :
    ObserverSpanningPacket L sites {e} := by
  refine ⟨Finset.singleton_nonempty e, not_spatiallyDisconnectedPacket_singleton L e, ?_⟩
  intro v hv
  rw [packetSiteSupport, Finset.singleton_biUnion]
  exact h hv

omit [Fintype E] [∀ v, Nonempty (A v)] in
/-- Hence the existence hypothesis of the sharp Steiner law is satisfied. -/
theorem exists_observerSpanningPacket_of_subset_support
    (L : FiniteLocalInteractionFamily V E A) {sites : Finset V} {e : E}
    (h : sites ⊆ L.support e) :
    ∃ packet : Finset E, ObserverSpanningPacket L sites packet :=
  ⟨{e}, observerSpanningPacket_singleton L h⟩

omit [Fintype E] [∀ v, Nonempty (A v)] in
/-- And the Steiner number is then at most one: the observer contrast can appear at first order. -/
theorem observerSteinerNumber_le_one_of_subset_support
    (L : FiniteLocalInteractionFamily V E A) {sites : Finset V} {e : E}
    (h : sites ⊆ L.support e) :
    observerSteinerNumber L sites ≤ 1 := by
  refine Nat.sInf_le ⟨{e}, observerSpanningPacket_singleton L h, ?_⟩
  exact Finset.card_singleton e

omit [Fintype E] [∀ v, Nonempty (A v)] in
/-- Conversely a spanning packet of at most one interaction is a singleton whose interaction
touches every queried site, so the bound above is sharp. -/
theorem exists_subset_support_of_observerSpanningPacket_card_le_one
    (L : FiniteLocalInteractionFamily V E A) {sites : Finset V} {packet : Finset E}
    (hpacket : ObserverSpanningPacket L sites packet) (hcard : packet.card ≤ 1) :
    ∃ e : E, sites ⊆ L.support e := by
  obtain ⟨e, he⟩ := hpacket.1
  refine ⟨e, ?_⟩
  have hsingle : packet = {e} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨he, fun x hx => Finset.card_le_one.mp hcard x hx e he⟩
  intro v hv
  have hmem := hpacket.2.2 hv
  rw [hsingle, packetSiteSupport, Finset.singleton_biUnion] at hmem
  exact hmem

end FiniteLocalInteractionFamily

end GaloisForLFunctions.HTGeometry
