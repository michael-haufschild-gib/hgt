import GaloisForLFunctions.HTGeometry.LocalWeightedPhaseEnsembleLaw
import GaloisForLFunctions.HTGeometry.ObserverTemporalPhaseSupportLaw

/-!
# Local observer-temporal support conservation

The weighted local-Hamiltonian birth law and the operational phase-support
identity are one theorem. Locality delays the loss of spectral constraints;
every lost constraint is exactly one temporal direction gained by the
limiting phase probability law.
-/

open Filter MeasureTheory Topology

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

noncomputable section

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)] [∀ v, Nonempty (A v)]

/-- Complete operational support conservation for a weighted local
Hermitian spectrum. -/
theorem existsUnique_localWeightedTemporalSupportConservation
    (L : FiniteLocalInteractionFamily V E A)
    (hL : HermitianInteractionFamily L)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℝ)
    (r : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∃! μ :
      ProbabilityMeasure (UnitAddTorus (∀ v, A v)),
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (L.weightedProductFrequency onsite hinj
              weight z g)
            (τ / g ^ r))
        (𝓝[>] 0) (𝓝 μ) ∧
      phaseLawTemporalDimension μ =
        temporalDimension
          (L.weightedProductSpectralJet onsite hinj
            weight hpos z) (r + 1) ∧
      phaseLawTemporalDimension μ +
          Module.finrank ℚ
            (phaseLawConstraintRationalSpace μ) =
        Module.finrank ℚ
          (ProjectiveRationalCharacter (∀ v, A v)) := by
  simpa [weightedProductSpectralJet] using!
    existsUnique_finiteAnalyticTemporalSupportConservation
      (fun config =>
        L.weightedProductEigenvalueBranch onsite hinj
          weight z config)
      (fun config =>
        L.weightedProductEigenvalueSeries onsite hinj
          weight hpos z config)
      (fun config =>
        L.weightedProductEigenvalueSeries_spec onsite hinj
          weight hpos z config)
      (L.weightedProductFrequency onsite hinj weight z)
      (fun config =>
        L.weightedProductEigenvalueBranch_eventually_real
          hL onsite hinj weight hpos z config)
      r hτ

/-- Complete operational support conservation for the same finite rational
observer carrier used to interrogate a weighted local Hermitian spectrum. -/
theorem existsUnique_localWeightedObserverTemporalSupportConservation
    {O : Type*} [AddCommGroup O] [Module ℚ O]
    [FiniteDimensional ℚ O]
    (L : FiniteLocalInteractionFamily V E A)
    (hL : HermitianInteractionFamily L)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℝ)
    (observe :
      O →ₗ[ℚ] ProjectiveRationalCharacter (∀ v, A v))
    (r : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∃! μ :
      ProbabilityMeasure (UnitAddTorus (∀ v, A v)),
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (L.weightedProductFrequency onsite hinj
              weight z g)
            (τ / g ^ r))
        (𝓝[>] 0) (𝓝 μ) ∧
      observerPhaseLawTemporalDimension μ observe =
        observerTemporalDimension
          (L.weightedProductSpectralJet onsite hinj
            weight hpos z) observe (r + 1) ∧
      observerPhaseLawTemporalDimension μ observe +
          Module.finrank ℚ
            (observerPhaseLawConstraintSpace μ observe) =
        Module.finrank ℚ O := by
  simpa [weightedProductSpectralJet] using!
    existsUnique_finiteAnalyticObserverSupportConservation
      (fun config =>
        L.weightedProductEigenvalueBranch onsite hinj
          weight z config)
      (fun config =>
        L.weightedProductEigenvalueSeries onsite hinj
          weight hpos z config)
      (fun config =>
        L.weightedProductEigenvalueSeries_spec onsite hinj
          weight hpos z config)
      (L.weightedProductFrequency onsite hinj weight z)
      (fun config =>
        L.weightedProductEigenvalueBranch_eventually_real
          hL onsite hinj weight hpos z config)
      observe r hτ

/-- **Local observer-temporal support law.** For every finite Hermitian
local system, every positive interaction weighting, every real switch-on
direction and every finite observer:

* its observer contrast is either the zero germ or cannot be born before
  the weighted connected-spanning cost; and
* at every inverse-power horizon, the unique limiting phase law has
  operational temporal dimension equal to resolved spectral-jet dimension,
  with exact dimension/constraint conservation.

No genericity or activation premise is used. -/
theorem localHermitianObserverTemporalSupportLaw
    {O : Type*} [AddCommGroup O] [Module ℚ O]
    [FiniteDimensional ℚ O]
    (L : FiniteLocalInteractionFamily V E A)
    (hL : HermitianInteractionFamily L)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℝ)
    (observe :
      O →ₗ[ℚ] ProjectiveRationalCharacter (∀ v, A v))
    (birthLower : ℕ)
    (hbirth :
      WeightedObserverSteinerLowerBound
        L sites weight birthLower)
    (observationOrder : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    (L.weightedSpectralObserverRay
        (complexOnsite onsite) hinj x alternative sites
        weight (fun e => z e)
        =ᶠ[𝓝 0] (fun _ => 0) ∨
      birthLower ≤
        (L.weightedSpectralObserverRaySeries
          (complexOnsite onsite) hinj x alternative sites
          weight hpos (fun e => z e)).order) ∧
    ∃! μ :
      ProbabilityMeasure (UnitAddTorus (∀ v, A v)),
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (L.weightedProductFrequency onsite hinj
              weight z g)
            (τ / g ^ observationOrder))
        (𝓝[>] 0) (𝓝 μ) ∧
      observerPhaseLawTemporalDimension μ observe =
        observerTemporalDimension
          (L.weightedProductSpectralJet onsite hinj
            weight hpos z) observe (observationOrder + 1) ∧
      observerPhaseLawTemporalDimension μ observe +
          Module.finrank ℚ
            (observerPhaseLawConstraintSpace μ observe) =
        Module.finrank ℚ O := by
  constructor
  · by_cases hzero :
      L.weightedSpectralObserverRay
          (complexOnsite onsite) hinj x alternative sites
          weight (fun e => z e)
        =ᶠ[𝓝 0] (fun _ => 0)
    · exact Or.inl hzero
    · exact Or.inr
        (L.weightedObserverSteinerLowerBound_le_weightedObserverSeries_order
          (complexOnsite onsite) hinj x alternative sites
          weight hpos (fun e => z e)
          hzero birthLower hbirth)
  · exact L.existsUnique_localWeightedObserverTemporalSupportConservation
      hL onsite hinj weight hpos z observe observationOrder hτ

end

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
