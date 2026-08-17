import GaloisForLFunctions.HTGeometry.LocalObserverTemporalSupportConservationLaw
import GaloisForLFunctions.HTGeometry.ObserverSteinerNumberLaw
import GaloisForLFunctions.HTGeometry.OnsiteEnergySeparation

/-!
# Explicit digit-local temporal-support capstone

The general local observer-temporal law asks for a separating product onsite energy and for a
weighted observer-Steiner lower bound.  Both inputs are canonical on a finite qudit register.
Base-`m` digit onsite energies separate all configurations, and the weighted observer-Steiner
number is unconditionally its own sharp lower bound.

The theorem below therefore retains only physical data: a finite local interaction family,
Hermiticity, positive switch-on weights, a real direction, and an observer.  Neither spectral
simplicity nor a geometric onset certificate is assumed.
-/

open Filter MeasureTheory Topology

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

noncomputable section

/-- **Explicit digit-local temporal-support capstone.**  On `n` sites with `m` local states,
base-`m` onsite energies discharge product-spectrum separation and the canonical weighted Steiner
number discharges the geometric birth premise. -/
theorem digitOnsiteLocalHermitianObserverTemporalSupportLaw
    (n m : ℕ) [NeZero m]
    {E O : Type*} [Fintype E] [DecidableEq E]
    [AddCommGroup O] [Module ℚ O] [FiniteDimensional ℚ O]
    (L : FiniteLocalInteractionFamily (Fin n) E (fun _ => Fin m))
    (hL : HermitianInteractionFamily L)
    (x alternative : Fin n → Fin m) (sites : Finset (Fin n))
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℝ)
    (observe : O →ₗ[ℚ] ProjectiveRationalCharacter (Fin n → Fin m))
    (observationOrder : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    (L.weightedSpectralObserverRay
        (complexOnsite (digitOnsite n m))
        (injective_onsiteProductEnergy_complexOnsite_digitOnsite n m)
        x alternative sites weight (fun e => z e) =ᶠ[𝓝 0] (fun _ => 0) ∨
      observerWeightedSteinerNumber L sites weight ≤
        (L.weightedSpectralObserverRaySeries
          (complexOnsite (digitOnsite n m))
          (injective_onsiteProductEnergy_complexOnsite_digitOnsite n m)
          x alternative sites weight hpos (fun e => z e)).order) ∧
    ∃! μ : ProbabilityMeasure (UnitAddTorus (Fin n → Fin m)),
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (L.weightedProductFrequency
              (digitOnsite n m)
              (injective_onsiteProductEnergy_complexOnsite_digitOnsite n m)
              weight z g)
            (τ / g ^ observationOrder))
        (𝓝[>] 0) (𝓝 μ) ∧
      observerPhaseLawTemporalDimension μ observe =
        observerTemporalDimension
          (L.weightedProductSpectralJet
            (digitOnsite n m)
            (injective_onsiteProductEnergy_complexOnsite_digitOnsite n m)
            weight hpos z) observe (observationOrder + 1) ∧
      observerPhaseLawTemporalDimension μ observe +
          Module.finrank ℚ (observerPhaseLawConstraintSpace μ observe) =
        Module.finrank ℚ O := by
  exact L.localHermitianObserverTemporalSupportLaw
    hL (digitOnsite n m)
    (injective_onsiteProductEnergy_complexOnsite_digitOnsite n m)
    x alternative sites weight hpos z observe
    (observerWeightedSteinerNumber L sites weight)
    (weightedObserverSteinerLowerBound_observerWeightedSteinerNumber
      L sites weight)
    observationOrder hτ

end

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry

