import GaloisForLFunctions.HTGeometry.WeightedInteractionPacketNewtonLaw

/-!
# Weighted observer-temporal Steiner law

Local interactions may approach zero at different rates.  The onset cost of
an observer-visible connected packet is then the sum of its interaction
weights, not its cardinality.  Every local spectral observer contrast is
therefore delayed by the least weighted connected packet spanning the
queried sites.
-/

open Filter Topology Asymptotics

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)] [∀ v, Nonempty (A v)]

/-- Positive integral cost of an interaction packet under an inhomogeneous
switch-on schedule. -/
def interactionPacketWeight
    (weight : E → ℕ) (packet : Finset E) : ℕ :=
  ∑ e ∈ packet, weight e

omit [∀ v, Nonempty (A v)] in
/-- Every observer packet obeys the weighted packet-depth law. -/
theorem spectralPacketSiteContrast_weightedMonomialRay_isBigO
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (packet : Finset E) (weight : E → ℕ)
    (hpos : ∀ e, 0 < weight e)
    (z : E → ℂ) :
    (fun g : ℂ =>
      spectralPacketSiteContrast L onsite hinj
        x alternative sites packet
          (fun e => g ^ weight e * z e))
      =O[𝓝 0]
    fun g : ℂ => ‖g‖ ^ interactionPacketWeight weight packet := by
  unfold spectralPacketSiteContrast dependentHigherCoordinateContrast
  unfold finsetMobiusResponse
  apply IsBigO.sum
  intro d hd
  let config :=
    dependentUpdateOnFinset x alternative (sites \ d)
  have hb :=
    spectralPacketResponse_globalWeightedMonomialRay_isBigO
      (L.productEigenvalueBranch onsite hinj config)
      (L.productEigenvalueBranch_spec onsite hinj config).1
      packet weight (fun e _ => hpos e) z
  exact hb.const_mul_left ((-1 : ℂ) ^ d.card)

/-- `r` is a lower bound for the weighted cost of every connected packet
spanning the observed sites. -/
def WeightedObserverSteinerLowerBound
    (L : FiniteLocalInteractionFamily V E A)
    (sites : Finset V) (weight : E → ℕ) (r : ℕ) : Prop :=
  ∀ packet,
    ObserverSpanningPacket L sites packet →
      r ≤ interactionPacketWeight weight packet

/-- **Weighted observer-temporal Steiner law.**  Along every positive
integer-weighted switch-on schedule, an observer contrast cannot appear
below the least weighted connected interaction packet spanning every
queried site. -/
theorem productSpectralInteractionShiftSiteContrast_weightedMonomialRay_isBigO
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (r : ℕ)
    (hr : WeightedObserverSteinerLowerBound L sites weight r)
    (z : E → ℂ) :
    (fun g : ℂ =>
      L.productSpectralInteractionShiftSiteContrast onsite hinj
        x alternative sites
          (fun e => g ^ weight e * z e))
      =O[𝓝 0]
    fun g : ℂ => ‖g‖ ^ r := by
  classical
  let ray : ℂ → (E → ℂ) :=
    fun g e => g ^ weight e * z e
  have hray : Tendsto ray (𝓝 0) (𝓝 0) := by
    have hc : Continuous ray := by
      dsimp [ray]
      fun_prop
    have hc0 : ContinuousAt ray 0 := hc.continuousAt
    change Tendsto ray (𝓝 0) (𝓝 (ray 0)) at hc0
    have hray0 : ray 0 = 0 := by
      funext e
      simp [ray, Nat.ne_of_gt (hpos e)]
    simpa [hray0] using hc0
  have hdecomp :=
    L.productSpectralInteractionShiftSiteContrast_eq_sum_observerSpanningPackets_germ
      onsite hinj x alternative sites
  have hpull := hdecomp.comp_tendsto hray
  have hsum :
      (fun g : ℂ =>
        ∑ packet ∈ observerSpanningPackets L sites,
          spectralPacketSiteContrast L onsite hinj
            x alternative sites packet (ray g))
        =O[𝓝 0]
      fun g : ℂ => ‖g‖ ^ r := by
    apply IsBigO.sum
    intro packet hpacket
    have hp : ObserverSpanningPacket L sites packet :=
      (Finset.mem_filter.mp hpacket).2
    exact
      (spectralPacketSiteContrast_weightedMonomialRay_isBigO
        L onsite hinj x alternative sites packet
          weight hpos z).trans
      (norm_pow_isBigO_norm_pow_of_le
        r (interactionPacketWeight weight packet)
          (hr packet hp))
  exact hsum.congr' hpull.symm Filter.EventuallyEq.rfl

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
