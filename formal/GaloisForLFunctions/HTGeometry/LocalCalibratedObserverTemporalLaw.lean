import GaloisForLFunctions.HTGeometry.LocalSiteMobiusPhaseCharacterLaw
import GaloisForLFunctions.HTGeometry.LocalWeightedPhaseEnsembleLaw
import GaloisForLFunctions.HTGeometry.ObserverTemporalPhaseSupportLaw

/-!
# Local calibrated observer-temporal law

Subtracting the decoupled spectrum places a local Hamiltonian in its
interaction picture. In this calibrated spectrum, one Boolean site-Möbius
observer is simultaneously:

* an integral projective phase character;
* a rational observer coordinate;
* a spectral-jet relation;
* and the local contrast controlled by weighted connected-spanning cost.

Thus locality, limiting-law phase support, and observer-temporal dimension
refer to one literal observable rather than three analogous constructions.
-/

open Filter MeasureTheory Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry
namespace FiniteLocalInteractionFamily

noncomputable section

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)] [∀ v, Nonempty (A v)]

/-- Weighted analytic product-energy branch after subtraction of its
decoupled energy. -/
noncomputable def weightedInteractionShiftBranch
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (weight : E → ℕ) (z : E → ℝ)
    (config : ∀ v, A v) (g : ℂ) : ℂ :=
  L.weightedProductEigenvalueBranch onsite hinj weight z config g -
    onsiteProductEnergy (complexOnsite onsite) config

omit [∀ (v : V), Nonempty (A v)] in
/-- Every calibrated weighted product-energy branch is analytic at zero. -/
theorem weightedInteractionShiftBranch_analyticAt
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℝ) (config : ∀ v, A v) :
    AnalyticAt ℂ
      (L.weightedInteractionShiftBranch onsite hinj
        weight z config) 0 := by
  exact
    (L.weightedProductEigenvalueBranch_analyticAt
      onsite hinj weight hpos z config).sub analyticAt_const

/-- Canonical scalar Taylor series of a calibrated weighted product-energy
branch. -/
noncomputable def weightedInteractionShiftSeries
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℝ) (config : ∀ v, A v) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  Classical.choose
    (L.weightedInteractionShiftBranch_analyticAt
      onsite hinj weight hpos z config)

omit [∀ (v : V), Nonempty (A v)] in
/-- The canonical calibrated series represents its interaction-picture
energy branch. -/
theorem weightedInteractionShiftSeries_spec
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℝ) (config : ∀ v, A v) :
    HasFPowerSeriesAt
      (L.weightedInteractionShiftBranch onsite hinj
        weight z config)
      (L.weightedInteractionShiftSeries onsite hinj
        weight hpos z config) 0 :=
  Classical.choose_spec
    (L.weightedInteractionShiftBranch_analyticAt
      onsite hinj weight hpos z config)

/-- Taylor jets of the calibrated weighted local spectrum. -/
noncomputable def weightedInteractionShiftSpectralJet
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℝ) (n : ℕ) (config : ∀ v, A v) : ℂ :=
  spectralTaylorJet
    (fun state =>
      L.weightedInteractionShiftSeries onsite hinj
        weight hpos z state)
    n config

/-- Real interaction-picture frequency obtained by subtracting the
decoupled product energy. -/
noncomputable def weightedInteractionShiftFrequency
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (weight : E → ℕ) (z : E → ℝ)
    (g : ℝ) (config : ∀ v, A v) : ℝ :=
  L.weightedProductFrequency onsite hinj weight z g config -
    onsiteProductEnergy onsite config

/-- Hermiticity makes every calibrated weighted branch real on the
physical positive-coupling germ. -/
theorem weightedInteractionShiftBranch_eventually_real
    (L : FiniteLocalInteractionFamily V E A)
    (hL : HermitianInteractionFamily L)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℝ) (config : ∀ v, A v) :
    ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      L.weightedInteractionShiftBranch onsite hinj
          weight z config (g : ℂ) =
        (L.weightedInteractionShiftFrequency onsite hinj
          weight z g config : ℂ) := by
  filter_upwards
    [L.weightedProductEigenvalueBranch_eventually_real
      hL onsite hinj weight hpos z config] with g hg
  rw [weightedInteractionShiftBranch,
    weightedInteractionShiftFrequency, hg]
  simp [onsiteProductEnergy, complexOnsite]

/-- A one-dimensional rational observer carrier generated by one
projective character. -/
def characterLineObserver
    {I : Type*} [Fintype I]
    (k : ProjectiveRationalCharacter I) :
    ℚ →ₗ[ℚ] ProjectiveRationalCharacter I where
  toFun q := q • k
  map_add' q p := by simp [add_smul]
  map_smul' q p := by simp [mul_smul]

omit [∀ (v : V), Nonempty (A v)] in
/-- The projective-character response of a local site-Möbius observer on
the calibrated spectrum is exactly the weighted local observer ray. -/
theorem projectiveCharacterResponse_weightedInteractionShift_siteMobius
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (hsites : sites.Nonempty)
    (weight : E → ℕ) (z : E → ℝ) :
    projectiveCharacterResponse
        (fun config =>
          L.weightedInteractionShiftBranch onsite hinj
            weight z config)
        (siteMobiusProjectiveCharacter
          x alternative sites hsites) =
      L.weightedSpectralObserverRay
        (complexOnsite onsite) hinj x alternative sites
        weight (fun e => (z e : ℂ)) := by
  funext g
  change
    (siteMobiusProjectiveCharacter
      x alternative sites hsites).1.sum
        (fun config m =>
          (m : ℂ) *
            L.weightedInteractionShiftBranch onsite hinj
              weight z config g) =
      L.productSpectralInteractionShiftSiteContrast
        (complexOnsite onsite) hinj x alternative sites
          (fun e => g ^ weight e * (z e : ℂ))
  simpa [weightedInteractionShiftBranch,
    weightedProductEigenvalueBranch,
    productSpectralInteractionShift,
    productSpectralInteractionShiftSiteContrast] using
      siteMobiusProjectiveCharacter_evaluate
        x alternative sites hsites
        (fun config =>
          L.productSpectralInteractionShift
            (complexOnsite onsite) hinj config
              (fun e => g ^ weight e * (z e : ℂ)))

/-- **Local calibrated constraint law.** The same projective character
whose phase is sampled by the observer remains an exact spectral-jet
relation through every order below the weighted connected-spanning cost.
No activation premise is required: an inactive character remains a
constraint at every order. -/
theorem siteMobiusProjectiveCharacter_mem_weightedConstraint
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (hsites : sites.Nonempty)
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℝ)
    (birthLower : ℕ)
    (hbirth :
      WeightedObserverSteinerLowerBound
        L sites weight birthLower) :
    siteMobiusProjectiveCharacter x alternative sites hsites ∈
      spectralConstraintFiltration
        (L.weightedInteractionShiftSpectralJet
          onsite hinj weight hpos z) birthLower := by
  let energy : (∀ v, A v) → ℂ → ℂ :=
    fun config =>
      L.weightedInteractionShiftBranch onsite hinj
        weight z config
  let series :
      (∀ v, A v) → FormalMultilinearSeries ℂ ℂ ℂ :=
    fun config =>
      L.weightedInteractionShiftSeries onsite hinj
        weight hpos z config
  let k : ProjectiveCharacter (∀ v, A v) :=
    siteMobiusProjectiveCharacter x alternative sites hsites
  have henergy :
      ∀ config, HasFPowerSeriesAt (energy config) (series config) 0 :=
    fun config =>
      L.weightedInteractionShiftSeries_spec
        onsite hinj weight hpos z config
  have hresponse :
      projectiveCharacterResponse energy k =
        L.weightedSpectralObserverRay
          (complexOnsite onsite) hinj x alternative sites
          weight (fun e => (z e : ℂ)) := by
    simpa [energy, k] using
      L.projectiveCharacterResponse_weightedInteractionShift_siteMobius
        onsite hinj x alternative sites hsites weight z
  by_cases hactive :
      SpectralCharacterActive (spectralTaylorJet series) k
  · have hseries :
        HasFPowerSeriesAt
          (projectiveCharacterResponse energy k)
          (projectiveCharacterSeries series k) 0 :=
      hasFPowerSeriesAt_projectiveCharacterResponse
        energy series henergy k
    have hactiveResponse :
        AnalyticSectorActive
          (projectiveCharacterResponse energy k) := by
      intro hzero
      have hseriesZero :
          projectiveCharacterSeries series k = 0 :=
        hseries.eq_zero_of_eventually hzero
      exact
        ((spectralCharacterActive_iff_characterSeries_ne_zero
          series k).mp hactive) hseriesZero
    have hraySeries :
        HasFPowerSeriesAt
          (L.weightedSpectralObserverRay
            (complexOnsite onsite) hinj x alternative sites
            weight (fun e => (z e : ℂ)))
          (projectiveCharacterSeries series k) 0 :=
      hseries.congr
        (Filter.Eventually.of_forall
          (fun g => congrFun hresponse g))
    have hrayActive :
        AnalyticSectorActive
          (L.weightedSpectralObserverRay
            (complexOnsite onsite) hinj x alternative sites
            weight (fun e => (z e : ℂ))) := by
      simpa [hresponse] using hactiveResponse
    have hlower :=
      L.weightedObserverSteinerLowerBound_le_analyticBirthOrder
        (complexOnsite onsite) hinj x alternative sites
        weight hpos birthLower hbirth
        (fun e => (z e : ℂ)) hraySeries hrayActive
    have hbirthOrder :=
      spectralCharacterBirthOrder_eq_series_order
        series k hactive
    rw [analyticBirthOrder, ← hbirthOrder] at hlower
    exact
      (mem_spectralConstraintFiltration_iff_le_birthOrder
        hactive birthLower).mpr hlower
  · exact
      (not_spectralCharacterActive_iff_forall_mem.mp hactive)
        birthLower

/-- **Local calibrated observer-temporal support law.** Before the weighted
connected-spanning cost, the unique limiting phase law keeps the exact same
local projective character equal to one almost surely. Simultaneously, the
phase-law dimension of its rational observer line equals the rank resolved
by its calibrated spectral jets, and dimension plus constraint rank is
exactly one. -/
theorem existsUnique_localCalibratedObserverTemporalSupport
    (L : FiniteLocalInteractionFamily V E A)
    (hL : HermitianInteractionFamily L)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (hsites : sites.Nonempty)
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℝ)
    (birthLower observationOrder : ℕ)
    (hbirth :
      WeightedObserverSteinerLowerBound
        L sites weight birthLower)
    (horizonBeforeBirth : observationOrder + 1 ≤ birthLower)
    {τ : ℝ} (hτ : 0 < τ) :
    let integralCharacter :=
      siteMobiusProjectiveCharacter x alternative sites hsites
    let rationalCharacter :=
      siteMobiusProjectiveRationalCharacter x alternative sites hsites
    let observe := characterLineObserver rationalCharacter
    ∃! μ :
      ProbabilityMeasure (UnitAddTorus (∀ v, A v)),
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (L.weightedInteractionShiftFrequency onsite hinj
              weight z g)
            (τ / g ^ observationOrder))
        (𝓝[>] 0) (𝓝 μ) ∧
      SpectralResolutionFourierLaw
        (fun state =>
          L.weightedInteractionShiftSeries onsite hinj
            weight hpos z state)
        observationOrder τ μ ∧
      (∀ k : ProjectiveCharacter (∀ v, A v),
        phaseLawConstraint μ k ↔
          k ∈ spectralConstraintFiltration
            (L.weightedInteractionShiftSpectralJet
              onsite hinj weight hpos z)
            (observationOrder + 1)) ∧
      phaseLawConstraint μ integralCharacter ∧
      observerPhaseLawTemporalDimension μ observe =
        observerTemporalDimension
          (L.weightedInteractionShiftSpectralJet
            onsite hinj weight hpos z)
          observe (observationOrder + 1) ∧
      observerPhaseLawTemporalDimension μ observe +
          Module.finrank ℚ
            (observerPhaseLawConstraintSpace μ observe) = 1 := by
  dsimp only
  let energy : (∀ v, A v) → ℂ → ℂ :=
    fun config =>
      L.weightedInteractionShiftBranch onsite hinj
        weight z config
  let series :
      (∀ v, A v) → FormalMultilinearSeries ℂ ℂ ℂ :=
    fun config =>
      L.weightedInteractionShiftSeries onsite hinj
        weight hpos z config
  let omega : ℝ → (∀ v, A v) → ℝ :=
    L.weightedInteractionShiftFrequency onsite hinj weight z
  let integralCharacter :=
    siteMobiusProjectiveCharacter x alternative sites hsites
  let rationalCharacter :=
    siteMobiusProjectiveRationalCharacter x alternative sites hsites
  let observe := characterLineObserver rationalCharacter
  obtain ⟨μ, hμ, hμunique⟩ :=
    existsUnique_finiteAnalyticTemporalPhaseSupport
      energy series
      (fun config =>
        L.weightedInteractionShiftSeries_spec
          onsite hinj weight hpos z config)
      omega
      (fun config =>
        L.weightedInteractionShiftBranch_eventually_real
          hL onsite hinj weight hpos z config)
      observationOrder hτ
  refine ⟨μ, ⟨hμ.1, ?_, hμ.2, ?_, ?_, ?_⟩, ?_⟩
  · exact finiteAnalyticTemporalPhase_completeFourierLaw
      energy series
      (fun config =>
        L.weightedInteractionShiftSeries_spec
          onsite hinj weight hpos z config)
      omega
      (fun config =>
        L.weightedInteractionShiftBranch_eventually_real
          hL onsite hinj weight hpos z config)
      observationOrder hτ μ hμ.1
  · apply (hμ.2 integralCharacter).mpr
    exact spectralConstraintFiltration_antitone
      (L.weightedInteractionShiftSpectralJet
        onsite hinj weight hpos z)
      horizonBeforeBirth
      (L.siteMobiusProjectiveCharacter_mem_weightedConstraint
        onsite hinj x alternative sites hsites weight hpos z
        birthLower hbirth)
  · exact finiteAnalyticObserverPhase_dimension_eq
      energy series
      (fun config =>
        L.weightedInteractionShiftSeries_spec
          onsite hinj weight hpos z config)
      omega
      (fun config =>
        L.weightedInteractionShiftBranch_eventually_real
          hL onsite hinj weight hpos z config)
      observe observationOrder hτ μ hμ.1
  · unfold observerPhaseLawTemporalDimension
    change
      Module.finrank ℚ ℚ -
            Module.finrank ℚ
              (observerPhaseLawConstraintSpace μ observe) +
          Module.finrank ℚ
            (observerPhaseLawConstraintSpace μ observe) =
        1
    have hle :
        Module.finrank ℚ
            (observerPhaseLawConstraintSpace μ observe) ≤
          Module.finrank ℚ ℚ :=
      Submodule.finrank_le _
    rw [Module.finrank_self] at hle ⊢
    omega
  · intro ν hν
    exact hμunique ν ⟨hν.1, hν.2.2.1⟩

end

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
