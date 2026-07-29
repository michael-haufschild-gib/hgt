import GaloisForLFunctions.HTGeometry.LocalSpectralObserverControlOrbitLaw

/-!
# Local birth law for observer-visible energy gaps

Energy gaps are the atoms from which projective quantum return is built.
This file specializes the universal linear-observer decomposition to those
physical gap coordinates.

Every controlled gap is its fixed onsite value plus an interaction-born
response.  For every activated control subset, that response is exactly the
sum of nonempty spatially indecomposable packet sectors.  A packet containing
`n` independently switchable channels is delayed to at least order `n`.
For Hermitian families and real controls, the analytic gap branches are
genuine real energies near the uncoupled point.
-/

open Filter Topology Asymptotics

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]

/-- Analytic energy gap between two selected simple product eigenbranches. -/
noncomputable def productEnergyGapBranch
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (left right : ∀ v, A v) (z : E → ℂ) : ℂ :=
  L.productEigenvalueBranch onsite hinj left z -
    L.productEigenvalueBranch onsite hinj right z

omit [∀ v, Nonempty (A v)] in
/-- Every controlled energy gap is its onsite gap plus the corresponding
linear spectral-observer response. -/
theorem productEnergyGapBranch_eq_onsite_add_response
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (left right : ∀ v, A v) (z : E → ℂ) :
    L.productEnergyGapBranch onsite hinj left right z =
      onsiteProductEnergy onsite left -
        onsiteProductEnergy onsite right +
      L.linearSpectralObserverResponse onsite hinj
        (spectralGapObserver left right) z := by
  unfold productEnergyGapBranch
  rw [L.linearSpectralObserverResponse_spectralGapObserver]
  unfold productSpectralInteractionShift
  ring

omit [∀ v, Nonempty (A v)] in
/-- Every selected controlled energy gap is analytic at the uncoupled
point. -/
theorem productEnergyGapBranch_analyticAt
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (left right : ∀ v, A v) :
    AnalyticAt ℂ
      (L.productEnergyGapBranch onsite hinj left right) 0 := by
  exact
    (L.productEigenvalueBranch_spec onsite hinj left).1.sub
      (L.productEigenvalueBranch_spec onsite hinj right).1

/-- Hermitian local families produce genuine real energy-gap branches along
the real coupling slice near zero. -/
theorem productEnergyGapBranch_im_eq_zero_eventually_realCoupling
    (L : FiniteLocalInteractionFamily V E A)
    (hL : HermitianInteractionFamily L)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (left right : ∀ v, A v) :
    ∀ᶠ coupling : E → ℝ in 𝓝 0,
      (L.productEnergyGapBranch
        (complexOnsite onsite) hinj left right
        (complexCoupling coupling)).im = 0 := by
  filter_upwards
    [L.productEigenvalueBranch_im_eq_zero_eventually_realCoupling
      hL onsite hinj left,
     L.productEigenvalueBranch_im_eq_zero_eventually_realCoupling
      hL onsite hinj right] with coupling hleft hright
  unfold productEnergyGapBranch
  rw [Complex.sub_im, hleft, hright, sub_self]

/-- **Connected birth law for every energy gap.**  After subtracting its
fixed onsite value, the gap seen in any restricted experiment is exactly,
as a germ, the sum of nonempty spatially indecomposable packet sectors
supported inside the activated controls. -/
theorem spectralGapRestrictedResponse_eq_sum_connectedSubpackets_germ
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (left right : ∀ v, A v)
    (active : Finset E) :
    (fun z =>
      L.productEnergyGapBranch onsite hinj left right
        (restrictInteractionPacket active z) -
      (onsiteProductEnergy onsite left -
        onsiteProductEnergy onsite right)) =ᶠ[𝓝 0]
      (fun z =>
        ∑ packet ∈ observerConnectedSubpackets L active,
          L.linearSpectralObserverPacketResponse onsite hinj
            (spectralGapObserver left right) packet z) := by
  have h :=
    L.linearSpectralObserverRestrictedResponse_eq_sum_connectedSubpackets_germ
      onsite hinj (spectralGapObserver left right) active
  filter_upwards [h] with z hz
  rw [productEnergyGapBranch_eq_onsite_add_response]
  rw [hz]
  ring

omit [∀ v, Nonempty (A v)] in
/-- Every `n`-channel irreducible energy-gap sector is delayed to order at
least `n` along every scalar coupling ray. -/
theorem spectralGapPacketResponse_couplingRay_isBigO
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (left right : ∀ v, A v)
    (packet : Finset E) (z : E → ℂ) :
    (fun g : ℂ =>
      L.linearSpectralObserverPacketResponse onsite hinj
        (spectralGapObserver left right) packet (g • z))
      =O[𝓝 0] fun g : ℂ => ‖g‖ ^ packet.card := by
  exact L.linearSpectralObserverPacketResponse_couplingRay_isBigO
    onsite hinj (spectralGapObserver left right) packet z

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
