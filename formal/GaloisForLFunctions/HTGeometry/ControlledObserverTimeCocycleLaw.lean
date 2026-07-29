import GaloisForLFunctions.HTGeometry.LocalObserverTimeGapBirthLaw
import GaloisForLFunctions.HTGeometry.EnergyGapCocycleLaw
import GaloisForLFunctions.RHTower.FiniteAtomicObserverTimeGapLaw

/-!
# Controlled observer-time cocycle law

This file closes the finite-system local-to-global bridge.  A finite
Hermitian local Hamiltonian supplies real controlled eigenvalue branches.
Their exact gap cocycle pushes the observer's pair weights to the abstract
observer-time gap measure.  Boolean packet projection commutes with formation
of that cocycle, and Hermiticity identifies its real atoms with genuine
spectral gaps near the uncoupled point.
-/

open Filter Topology MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]

/-- Real part of a controlled product eigenvalue branch.  For a Hermitian
family this is the branch itself along real controls near zero. -/
noncomputable def controlledProductObserverEnergy
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (coupling : E → ℝ) (config : ∀ v, A v) : ℝ :=
  (L.productEigenvalueBranch
    (complexOnsite onsite) hinj config
    (complexCoupling coupling)).re

/-- Finite observer spectrum carried by all selected controlled product
branches with prescribed observer weights. -/
noncomputable def controlledProductObserverSpectrum
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (weight : (∀ v, A v) → ℝ)
    (coupling : E → ℝ) : Measure ℝ :=
  RHTower.finiteAtomicObserverSpectrum weight
    (L.controlledProductObserverEnergy onsite hinj coupling)

omit [∀ v, Nonempty (A v)] in
theorem controlledProductObserverSpectrum_isProbabilityMeasure
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (weight : (∀ v, A v) → ℝ)
    (hweight : ∀ config, 0 ≤ weight config)
    (hsum : ∑ config, weight config = 1)
    (coupling : E → ℝ) :
    IsProbabilityMeasure
      (L.controlledProductObserverSpectrum
        onsite hinj weight coupling) := by
  unfold controlledProductObserverSpectrum
  exact RHTower.finiteAtomicObserverSpectrum_isProbabilityMeasure
    weight _ hweight hsum

omit [∀ v, Nonempty (A v)] in
/-- **Controlled finite-spectrum bridge.**  The abstract observer-time gap
measure of the controlled spectrum is exactly the weighted atomic pushforward
of its complete energy-gap cocycle. -/
theorem observerTimeGapMeasure_controlledProductObserverSpectrum
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (weight : (∀ v, A v) → ℝ)
    (coupling : E → ℝ) :
    RHTower.observerTimeGapMeasure
        (L.controlledProductObserverSpectrum
          onsite hinj weight coupling) =
      RHTower.finiteAtomicObserverGapMeasure weight
        (L.controlledProductObserverEnergy onsite hinj coupling) := by
  exact RHTower.observerTimeGapMeasure_finiteAtomicObserverSpectrum
    weight _

omit [∀ v, Nonempty (A v)] in
/-- **Controlled return-cocycle law.**  At every control setting and every
time, the complete projective return record is the Fourier sum of the
observer-weighted exact energy-gap cocycle. -/
theorem projectiveReturnRecord_controlledProductObserverSpectrum
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (weight : (∀ v, A v) → ℝ)
    (hweight : ∀ config, 0 ≤ weight config)
    (hsum : ∑ config, weight config = 1)
    (coupling : E → ℝ) (t : ℝ) :
    (RHTower.projectiveReturnRecord
        (L.controlledProductObserverSpectrum
          onsite hinj weight coupling) t : ℂ) =
      ∑ p : (∀ v, A v) × (∀ v, A v),
        ((weight p.1 * weight p.2 : ℝ) : ℂ) *
          Complex.exp
            ((t * energyGapCocycle
              (L.controlledProductObserverEnergy
                onsite hinj coupling) p.1 p.2 : ℝ) *
              Complex.I) := by
  exact RHTower.projectiveReturnRecord_finiteAtomicObserverSpectrum
    weight
    (L.controlledProductObserverEnergy onsite hinj coupling)
    hweight hsum t

omit [∀ v, Nonempty (A v)] in
/-- Each atom location in the controlled observer-time measure is the real
part of the corresponding analytic energy-gap branch. -/
theorem controlledProductObserverGap_eq_productEnergyGapBranch_re
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (coupling : E → ℝ) (left right : ∀ v, A v) :
    energyGapCocycle
        (L.controlledProductObserverEnergy onsite hinj coupling)
        left right =
      (L.productEnergyGapBranch
        (complexOnsite onsite) hinj left right
        (complexCoupling coupling)).re := by
  rfl

/-- For Hermitian local dynamics, each complex analytic gap branch is exactly
the real atom location of the controlled observer-time measure near zero
real coupling. -/
theorem productEnergyGapBranch_eq_controlledProductObserverGap_eventually
    (L : FiniteLocalInteractionFamily V E A)
    (hL : HermitianInteractionFamily L)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (left right : ∀ v, A v) :
    ∀ᶠ coupling : E → ℝ in 𝓝 0,
      L.productEnergyGapBranch
          (complexOnsite onsite) hinj left right
          (complexCoupling coupling) =
        ((energyGapCocycle
          (L.controlledProductObserverEnergy onsite hinj coupling)
          left right : ℝ) : ℂ) := by
  filter_upwards
    [L.productEnergyGapBranch_im_eq_zero_eventually_realCoupling
      hL onsite hinj left right] with coupling him
  apply Complex.ext
  · rfl
  · simpa using him

omit [∀ v, Nonempty (A v)] in
/-- Packet projection of every controlled spectral gap is exactly the
difference of the endpoint-energy packet sectors. -/
theorem controlledProductObserverGap_packetResponse
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (packet : Finset E) (z : E → ℂ)
    (left right : ∀ v, A v) :
    spectralPacketResponse
        (L.productEnergyGapBranch onsite hinj left right)
        packet z =
      spectralPacketResponse
          (L.productEigenvalueBranch onsite hinj left) packet z -
        spectralPacketResponse
          (L.productEigenvalueBranch onsite hinj right) packet z := by
  exact spectralPacketResponse_energyGapCocycle
    (fun coupling config =>
      L.productEigenvalueBranch onsite hinj config coupling)
    packet z left right

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
