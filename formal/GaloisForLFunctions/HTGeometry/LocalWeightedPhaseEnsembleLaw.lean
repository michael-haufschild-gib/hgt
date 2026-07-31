import GaloisForLFunctions.HTGeometry.FiniteAnalyticPhaseEnsembleWallCrossingLaw
import GaloisForLFunctions.HTGeometry.ArbitrarySpectrumTemporalWallCrossingLaw
import GaloisForLFunctions.HTGeometry.HermitianLocalSpectralObserverLaw
import GaloisForLFunctions.HTGeometry.ObserverTemporalDimensionCascadeLaw
import GaloisForLFunctions.HTGeometry.WeightedObserverTemporalBirthLaw

/-!
# Local weighted phase-ensemble law

For every finite Hermitian local interaction family with a simple
decoupled product spectrum, every positive integer-weighted switch-on
schedule produces analytic real energy branches.  The complete
time-sampled phase probability law therefore has a unique weak limit at
every inverse-power observation horizon.
-/

open Filter MeasureTheory Topology

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)] [∀ v, Nonempty (A v)]

/-- Analytic product-energy branch along an inhomogeneous switch-on
schedule. -/
noncomputable def weightedProductEigenvalueBranch
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (weight : E → ℕ) (z : E → ℝ)
    (config : ∀ v, A v) (g : ℂ) : ℂ :=
  L.productEigenvalueBranch (complexOnsite onsite) hinj config
    (fun e => g ^ weight e * z e)

omit [∀ (v : V), Nonempty (A v)] in
/-- Every weighted product-energy branch is analytic at zero. -/
theorem weightedProductEigenvalueBranch_analyticAt
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℝ) (config : ∀ v, A v) :
    AnalyticAt ℂ
      (L.weightedProductEigenvalueBranch onsite hinj
        weight z config) 0 := by
  let coupling : ℂ → (E → ℂ) :=
    fun g e => g ^ weight e * z e
  have hcoupling : AnalyticAt ℂ coupling 0 := by
    dsimp [coupling]
    apply AnalyticAt.pi
    intro e
    fun_prop
  have hcoupling0 : coupling 0 = 0 := by
    funext e
    simp [coupling, Nat.ne_of_gt (hpos e)]
  have hbranch :=
    (L.productEigenvalueBranch_spec
      (complexOnsite onsite) hinj config).1
  unfold weightedProductEigenvalueBranch
  exact hbranch.comp_of_eq hcoupling hcoupling0

/-- Canonical scalar Taylor series of a weighted product-energy branch. -/
noncomputable def weightedProductEigenvalueSeries
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℝ) (config : ∀ v, A v) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  Classical.choose
    (L.weightedProductEigenvalueBranch_analyticAt
      onsite hinj weight hpos z config)

omit [∀ (v : V), Nonempty (A v)] in
/-- The canonical weighted series represents its energy branch. -/
theorem weightedProductEigenvalueSeries_spec
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℝ) (config : ∀ v, A v) :
    HasFPowerSeriesAt
      (L.weightedProductEigenvalueBranch onsite hinj
        weight z config)
      (L.weightedProductEigenvalueSeries onsite hinj
        weight hpos z config) 0 :=
  Classical.choose_spec
    (L.weightedProductEigenvalueBranch_analyticAt
      onsite hinj weight hpos z config)

/-- Taylor jets of the complete weighted local product spectrum. -/
noncomputable def weightedProductSpectralJet
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℝ) (n : ℕ) (config : ∀ v, A v) : ℂ :=
  spectralTaylorJet
    (fun state =>
      L.weightedProductEigenvalueSeries onsite hinj
        weight hpos z state)
    n config

/-- Physical real frequency selected from the weighted analytic branch. -/
noncomputable def weightedProductFrequency
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (weight : E → ℕ) (z : E → ℝ)
    (g : ℝ) (config : ∀ v, A v) : ℝ :=
  (L.weightedProductEigenvalueBranch onsite hinj
    weight z config g).re

/-- Hermiticity makes every weighted product-energy branch real on the
physical positive-coupling germ. -/
theorem weightedProductEigenvalueBranch_eventually_real
    (L : FiniteLocalInteractionFamily V E A)
    (hL : HermitianInteractionFamily L)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℝ) (config : ∀ v, A v) :
    ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      L.weightedProductEigenvalueBranch onsite hinj
          weight z config (g : ℂ) =
        (L.weightedProductFrequency onsite hinj
          weight z g config : ℂ) := by
  let realCoupling : ℝ → (E → ℝ) :=
    fun g e => g ^ weight e * z e
  have hcoupling : Tendsto realCoupling (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous realCoupling := by
      dsimp [realCoupling]
      fun_prop
    have hc0 : ContinuousAt realCoupling 0 := hc.continuousAt
    have hzero : realCoupling 0 = 0 := by
      funext e
      simp [realCoupling, Nat.ne_of_gt (hpos e)]
    change
      Tendsto realCoupling
        (𝓝 0 ⊓ 𝓟 (Set.Ioi 0)) (𝓝 0)
    rw [ContinuousAt] at hc0
    simpa only [hzero] using hc0.mono_left inf_le_left
  have hreal :=
    L.productEigenvalueBranch_im_eq_zero_eventually_realCoupling
      hL onsite hinj config
  have hpull := hcoupling.eventually hreal
  filter_upwards [hpull] with g hg
  have hcouplingEq :
      complexCoupling (realCoupling g) =
        fun e => (g : ℂ) ^ weight e * z e := by
    funext e
    simp [complexCoupling, realCoupling]
  have him :
      (L.weightedProductEigenvalueBranch onsite hinj
        weight z config (g : ℂ)).im = 0 := by
    simpa [weightedProductEigenvalueBranch, hcouplingEq] using hg
  apply Complex.ext
  · simp [weightedProductFrequency]
  · simpa [weightedProductFrequency] using him

/-- **Complete local weighted phase-law wall crossing.** Every finite
Hermitian local quantum system with a simple decoupled product spectrum,
every positive integer interaction weighting and every real switch-on
direction has one unique limiting phase probability law at every
inverse-power observation horizon. -/
theorem existsUnique_localWeightedPhaseEnsemble_limit
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
        (𝓝[>] 0) (𝓝 μ) := by
  apply existsUnique_finiteAnalyticPhaseEnsemble_limit
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
  · intro config
    exact L.weightedProductEigenvalueBranch_eventually_real
      hL onsite hinj weight hpos z config
  · exact hτ

/-- **Local observer-temporal Newton law.** For every finite Hermitian
local system, positive integer interaction weighting, real switch-on
direction and finite observer:

* the observer contrast is either the zero germ or its exact birth order is
  at least every certified weighted connected-spanning cost; and
* at every inverse-power horizon the complete phase probability law has one
  unique weak limit.

The statement has no genericity or activation premise. -/
theorem localHermitianObserverTemporalNewtonLaw
    (L : FiniteLocalInteractionFamily V E A)
    (hL : HermitianInteractionFamily L)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℝ)
    (birthLower : ℕ)
    (hbirth :
      WeightedObserverSteinerLowerBound
        L sites weight birthLower)
    (jetResolution : ℕ)
    (observationOrder : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    (L.weightedSpectralObserverRay
        (complexOnsite onsite) hinj x alternative sites
        weight (fun e => z e)
        =ᶠ[𝓝 0] (fun _ => 0) ∨
      birthLower ≤
        (L.weightedSpectralObserverRaySeries
          (complexOnsite onsite) hinj x alternative sites
          weight hpos (fun e => z e)).order) ∧
    (temporalDimension
        (L.weightedProductSpectralJet onsite hinj
          weight hpos z) jetResolution +
      Module.finrank ℚ
        (rationalSpectralConstraintSpace
          (L.weightedProductSpectralJet onsite hinj
            weight hpos z) jetResolution) =
      Module.finrank ℚ
        (ProjectiveRationalCharacter (∀ v, A v))) ∧
    ∃! μ :
      ProbabilityMeasure (UnitAddTorus (∀ v, A v)),
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (L.weightedProductFrequency onsite hinj
              weight z g)
            (τ / g ^ observationOrder))
        (𝓝[>] 0) (𝓝 μ) := by
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
  constructor
  · exact temporalDimension_add_constraintFinrank
      (L.weightedProductSpectralJet onsite hinj
        weight hpos z) jetResolution
  · exact L.existsUnique_localWeightedPhaseEnsemble_limit
      hL onsite hinj weight hpos z observationOrder hτ

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
