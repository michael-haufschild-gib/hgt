import GaloisForLFunctions.HTGeometry.LocalObserverTimeGapBirthLaw

/-!
# Observer-time law inside arbitrary control architectures

The ambient set of possible local interaction channels need not be finite.
Every physical experiment activates only a finite labelled subarchitecture.
Restricting an arbitrary interaction family to such a finite set preserves
its site supports, local matrices, Hermiticity, and the connected
observer-time birth law.

Thus the local law applies uniformly to every finite experiment inside an
arbitrarily large or infinite control architecture.  It does not postulate an
infinite operator sum.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

/-- Restriction of an arbitrary interaction-label architecture to one finite
experimental set of channels. -/
def restrictInteractionLabels
    (L : FiniteLocalInteractionFamily V E A)
    (labels : Finset E) :
    FiniteLocalInteractionFamily V {e : E // e ∈ labels} A where
  support e := L.support e.1
  interaction e := L.interaction e.1

omit [DecidableEq E] in
@[simp]
theorem restrictInteractionLabels_support
    (L : FiniteLocalInteractionFamily V E A)
    (labels : Finset E) (e : {e : E // e ∈ labels}) :
    (L.restrictInteractionLabels labels).support e =
      L.support e.1 := rfl

omit [DecidableEq E] in
/-- Restricting labels preserves Hermiticity. -/
theorem restrictInteractionLabels_hermitian
    (L : FiniteLocalInteractionFamily V E A)
    (hL : ∀ e, (L.globalInteraction e).IsHermitian)
    (labels : Finset E) :
    HermitianInteractionFamily
      (L.restrictInteractionLabels labels) := by
  intro e
  exact hL e.1

/-- **Arbitrary-architecture finite-experiment law.**  Every finite
experiment cut from any, possibly infinite, local control architecture has
the exact connected-packet birth decomposition for every selected energy
gap and every activated control subset. -/
theorem finiteExperiment_spectralGap_connectedBirthLaw
    [∀ v, Nonempty (A v)]
    (L : FiniteLocalInteractionFamily V E A)
    (labels : Finset E)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (left right : ∀ v, A v)
    (active : Finset {e : E // e ∈ labels}) :
    (fun z =>
      (L.restrictInteractionLabels labels).productEnergyGapBranch
          onsite hinj left right
          (restrictInteractionPacket active z) -
        (onsiteProductEnergy onsite left -
          onsiteProductEnergy onsite right)) =ᶠ[𝓝 0]
      (fun z =>
        ∑ packet ∈
            (L.restrictInteractionLabels labels).observerConnectedSubpackets
              active,
          (L.restrictInteractionLabels labels).linearSpectralObserverPacketResponse
              onsite hinj
              (spectralGapObserver left right) packet z) := by
  exact
    (L.restrictInteractionLabels labels).spectralGapRestrictedResponse_eq_sum_connectedSubpackets_germ
        onsite hinj left right active

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
