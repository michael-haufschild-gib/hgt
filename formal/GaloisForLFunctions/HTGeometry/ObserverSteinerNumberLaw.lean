import GaloisForLFunctions.HTGeometry.WeightedObserverTemporalSteinerLaw

/-!
# The observer Steiner number is the sharp onset constant

The observer-onset laws are stated against an arbitrary lower bound `r` for the cost of every
connected packet spanning the queried sites.  That interface has a canonical inhabitant: the
least such cost, taken over all spanning packets.  It is a lower bound unconditionally, and when a
spanning packet exists it is the largest one, so the interface is exactly `r ≤` the Steiner number.
When no spanning packet exists every `r` qualifies and the onset laws hold at every order.

The weighted interface is not independent either: for a switch-on schedule with positive weights
the unweighted bound implies the weighted one, since a packet's cardinality never exceeds its
weight.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)] [∀ v, Nonempty (A v)]

/-! ## Monotonicity, and the vacuous case -/

theorem ObserverSteinerLowerBound.mono
    {L : FiniteLocalInteractionFamily V E A} {sites : Finset V} {r r' : ℕ}
    (hr : ObserverSteinerLowerBound L sites r) (hle : r' ≤ r) :
    ObserverSteinerLowerBound L sites r' :=
  fun packet hpacket => hle.trans (hr packet hpacket)

theorem WeightedObserverSteinerLowerBound.mono
    {L : FiniteLocalInteractionFamily V E A} {sites : Finset V} {weight : E → ℕ} {r r' : ℕ}
    (hr : WeightedObserverSteinerLowerBound L sites weight r) (hle : r' ≤ r) :
    WeightedObserverSteinerLowerBound L sites weight r' :=
  fun packet hpacket => hle.trans (hr packet hpacket)

/-- With no spanning packet the bound is vacuous at every order. -/
theorem observerSteinerLowerBound_of_not_exists
    {L : FiniteLocalInteractionFamily V E A} {sites : Finset V}
    (h : ¬ ∃ packet, ObserverSpanningPacket L sites packet) (r : ℕ) :
    ObserverSteinerLowerBound L sites r :=
  fun packet hpacket => absurd ⟨packet, hpacket⟩ h

/-! ## The unweighted Steiner number -/

/-- The least cardinality of a connected packet spanning the queried sites. -/
noncomputable def observerSteinerNumber
    (L : FiniteLocalInteractionFamily V E A) (sites : Finset V) : ℕ :=
  sInf {n : ℕ | ∃ packet : Finset E, ObserverSpanningPacket L sites packet ∧ packet.card = n}

/-- The Steiner number is a lower bound, unconditionally. -/
theorem observerSteinerLowerBound_observerSteinerNumber
    (L : FiniteLocalInteractionFamily V E A) (sites : Finset V) :
    ObserverSteinerLowerBound L sites (observerSteinerNumber L sites) := by
  intro packet hpacket
  exact Nat.sInf_le ⟨packet, hpacket, rfl⟩

/-- It is the largest lower bound as soon as one spanning packet exists. -/
theorem le_observerSteinerNumber
    {L : FiniteLocalInteractionFamily V E A} {sites : Finset V} {r : ℕ}
    (hexists : ∃ packet, ObserverSpanningPacket L sites packet)
    (hr : ObserverSteinerLowerBound L sites r) :
    r ≤ observerSteinerNumber L sites := by
  obtain ⟨packet, hpacket⟩ := hexists
  have hne : {n : ℕ | ∃ p : Finset E, ObserverSpanningPacket L sites p ∧ p.card = n}.Nonempty :=
    ⟨packet.card, packet, hpacket, rfl⟩
  obtain ⟨p, hp, hcard⟩ := Nat.sInf_mem hne
  rw [observerSteinerNumber, ← hcard]
  exact hr p hp

/-- **The unweighted interface, characterized.**  With a spanning packet present, `r` is an
observer Steiner lower bound exactly when it is at most the Steiner number. -/
theorem observerSteinerLowerBound_iff
    {L : FiniteLocalInteractionFamily V E A} {sites : Finset V} {r : ℕ}
    (hexists : ∃ packet, ObserverSpanningPacket L sites packet) :
    ObserverSteinerLowerBound L sites r ↔ r ≤ observerSteinerNumber L sites :=
  ⟨fun hr => le_observerSteinerNumber hexists hr,
    fun hle => (observerSteinerLowerBound_observerSteinerNumber L sites).mono hle⟩

/-! ## The weighted Steiner number -/

/-- The least weighted cost of a connected packet spanning the queried sites. -/
noncomputable def observerWeightedSteinerNumber
    (L : FiniteLocalInteractionFamily V E A) (sites : Finset V) (weight : E → ℕ) : ℕ :=
  sInf {n : ℕ | ∃ packet : Finset E, ObserverSpanningPacket L sites packet ∧
    interactionPacketWeight weight packet = n}

/-- The weighted Steiner number is a weighted lower bound, unconditionally. -/
theorem weightedObserverSteinerLowerBound_observerWeightedSteinerNumber
    (L : FiniteLocalInteractionFamily V E A) (sites : Finset V) (weight : E → ℕ) :
    WeightedObserverSteinerLowerBound L sites weight
      (observerWeightedSteinerNumber L sites weight) := by
  intro packet hpacket
  exact Nat.sInf_le ⟨packet, hpacket, rfl⟩

/-- It is the largest weighted lower bound as soon as one spanning packet exists. -/
theorem le_observerWeightedSteinerNumber
    {L : FiniteLocalInteractionFamily V E A} {sites : Finset V} {weight : E → ℕ} {r : ℕ}
    (hexists : ∃ packet, ObserverSpanningPacket L sites packet)
    (hr : WeightedObserverSteinerLowerBound L sites weight r) :
    r ≤ observerWeightedSteinerNumber L sites weight := by
  obtain ⟨packet, hpacket⟩ := hexists
  have hne : {n : ℕ | ∃ p : Finset E, ObserverSpanningPacket L sites p ∧
      interactionPacketWeight weight p = n}.Nonempty :=
    ⟨interactionPacketWeight weight packet, packet, hpacket, rfl⟩
  obtain ⟨p, hp, hcost⟩ := Nat.sInf_mem hne
  rw [observerWeightedSteinerNumber, ← hcost]
  exact hr p hp

/-- **The weighted interface, characterized.** -/
theorem weightedObserverSteinerLowerBound_iff
    {L : FiniteLocalInteractionFamily V E A} {sites : Finset V} {weight : E → ℕ} {r : ℕ}
    (hexists : ∃ packet, ObserverSpanningPacket L sites packet) :
    WeightedObserverSteinerLowerBound L sites weight r ↔
      r ≤ observerWeightedSteinerNumber L sites weight :=
  ⟨fun hr => le_observerWeightedSteinerNumber hexists hr,
    fun hle =>
      (weightedObserverSteinerLowerBound_observerWeightedSteinerNumber L sites weight).mono hle⟩

/-! ## The weighted bound is implied by the unweighted one -/

/-- A packet's cardinality never exceeds its weight when every interaction costs at least one. -/
theorem card_le_interactionPacketWeight
    {weight : E → ℕ} (hpos : ∀ e, 1 ≤ weight e) (packet : Finset E) :
    packet.card ≤ interactionPacketWeight weight packet := by
  have h := Finset.card_nsmul_le_sum packet weight 1 (fun e _ => hpos e)
  simpa [interactionPacketWeight] using h

/-- **Weighted from unweighted.**  For a positive switch-on schedule the unweighted observer
Steiner bound is already a weighted one, so the weighted interface needs no separate input. -/
theorem weightedObserverSteinerLowerBound_of_observerSteinerLowerBound
    {L : FiniteLocalInteractionFamily V E A} {sites : Finset V} {weight : E → ℕ} {r : ℕ}
    (hpos : ∀ e, 1 ≤ weight e) (hr : ObserverSteinerLowerBound L sites r) :
    WeightedObserverSteinerLowerBound L sites weight r :=
  fun packet hpacket =>
    (hr packet hpacket).trans (card_le_interactionPacketWeight hpos packet)

/-- Consequently the unweighted Steiner number bounds the weighted one from below. -/
theorem observerSteinerNumber_le_observerWeightedSteinerNumber
    {L : FiniteLocalInteractionFamily V E A} {sites : Finset V} {weight : E → ℕ}
    (hpos : ∀ e, 1 ≤ weight e)
    (hexists : ∃ packet, ObserverSpanningPacket L sites packet) :
    observerSteinerNumber L sites ≤ observerWeightedSteinerNumber L sites weight :=
  le_observerWeightedSteinerNumber hexists
    (weightedObserverSteinerLowerBound_of_observerSteinerLowerBound hpos
      (observerSteinerLowerBound_observerSteinerNumber L sites))

end FiniteLocalInteractionFamily

end GaloisForLFunctions.HTGeometry
