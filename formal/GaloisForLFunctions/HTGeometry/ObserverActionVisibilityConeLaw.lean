import GaloisForLFunctions.HTGeometry.TemporalPhaseValuationTomographyLaw
import GaloisForLFunctions.HTGeometry.SpectralCharacterReplicaHeightLaw
import GaloisForLFunctions.HTGeometry.ObserverTimeFourierValuationAtlasLaw
import GaloisForLFunctions.HTGeometry.LocalCalibratedObserverTemporalLaw
import GaloisForLFunctions.HTGeometry.LocalMobiusReplicaHeightLaw
import GaloisForLFunctions.HTGeometry.FidelityReplicaCharacterCoefficientLaw

/-!
# Observer-action visibility cone

One projective spectral character has two independent observation costs.
Its analytic birth order is the first inverse-power time horizon at which
the limiting phase law unlocks it.  Its positive coefficient mass is the
first fidelity-replica order in which the same character can occur.

The pair is an exact lower-left corner: it is attained, and every
time-horizon/replica-order pair that sees the character lies northeast of
it.  This turns temporal activation and recurrence detector order into two
filtrations of one literal spectral relation.
-/

open Filter MeasureTheory Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Exact minimum fidelity-replica order of a projective character. -/
def projectiveCharacterReplicaHeight
    {d : Type*} [Fintype d]
    (k : ProjectiveCharacter d) : ℕ :=
  spectralCharacterPositiveMass (fun i => k.1 i)

/-- Every projective character is balanced when written as a coefficient
function on a finite spectrum. -/
theorem projectiveCharacter_spectralCharacterBalanced
    {d : Type*} [Fintype d]
    (k : ProjectiveCharacter d) :
    SpectralCharacterBalanced (fun i => k.1 i) := by
  classical
  unfold SpectralCharacterBalanced
  calc
    (∑ i, k.1 i) =
        k.1.sum (fun _ m => m) := by
      symm
      rw [Finsupp.sum_fintype]
      intro i
      simp
    _ = 0 := k.2

/-- A projective character is visible at temporal order `r` and replica
order `m` when the limiting phase law has unlocked it and an `m`-replica
fidelity expansion can realize it. -/
def PhaseReplicaCharacterVisibleAt
    {d : Type*} [Fintype d]
    (atlas : ℕ → ProbabilityMeasure (UnitAddTorus d))
    (r m : ℕ) (k : ProjectiveCharacter d) : Prop :=
  PhaseLawCharacterUnlocked (atlas r) k ∧
    SpectralCharacterReplicaRealizes m (fun i => k.1 i)

/-- Operational visibility in an actual full-support survival-fidelity
moment: the phase law has unlocked the character and its collected
multinomial coefficient is strictly positive. -/
def FidelityMomentCharacterVisibleAt
    {d : Type*} [Fintype d] [DecidableEq d]
    (atlas : ℕ → ProbabilityMeasure (UnitAddTorus d))
    (weight : d → ℝ)
    (r m : ℕ) (k : ProjectiveCharacter d) : Prop :=
  PhaseLawCharacterUnlocked (atlas r) k ∧
    0 < fidelityReplicaCharacterCoefficient
      weight m (fun i => k.1 i)

/-- **Exact observer-action visibility corner.** For every active
projective character of a finite analytic real spectrum, its analytic
birth order and replica height are jointly attained.  Every temporal
horizon and replica order capable of seeing that character is at least
this pair coordinatewise. -/
theorem phaseReplicaCharacterVisible_exactCorner
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    {τ : ℝ} (hτ : 0 < τ)
    (atlas : ℕ → ProbabilityMeasure (UnitAddTorus d))
    (hatlas : ∀ r,
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 (atlas r)))
    (k : ProjectiveCharacter d)
    (hactive :
      SpectralCharacterActive (spectralTaylorJet series) k) :
    let birth :=
      spectralCharacterBirthOrder
        (spectralTaylorJet series) k hactive
    let height := projectiveCharacterReplicaHeight k
    PhaseReplicaCharacterVisibleAt atlas birth height k ∧
      ∀ r m,
        PhaseReplicaCharacterVisibleAt atlas r m k →
          birth ≤ r ∧ height ≤ m := by
  dsimp only
  constructor
  · constructor
    · exact
        (finiteAnalyticPhaseLaw_characterUnlocked_iff_birthOrder_le
          energy series henergy omega hreal hτ
          (spectralCharacterBirthOrder
            (spectralTaylorJet series) k hactive)
          (atlas
            (spectralCharacterBirthOrder
              (spectralTaylorJet series) k hactive))
          (hatlas
            (spectralCharacterBirthOrder
              (spectralTaylorJet series) k hactive))
          k hactive).mpr le_rfl
    · exact
        spectralCharacterReplicaRealizes_positiveMass_of_balanced
          (projectiveCharacter_spectralCharacterBalanced k)
  · intro r m hvisible
    constructor
    · exact
        (finiteAnalyticPhaseLaw_characterUnlocked_iff_birthOrder_le
          energy series henergy omega hreal hτ r
          (atlas r) (hatlas r) k hactive).mp hvisible.1
    · exact
        spectralCharacterPositiveMass_le_of_replicaRealizes
          hvisible.2

/-- **Exact northeast visibility cone.** In a nonempty finite analytic
spectrum, an active character occurs at temporal order `r` and replica order
`m` exactly when `r` is at least its birth order and `m` is at least its
replica height. -/
theorem phaseReplicaCharacterVisible_iff_corner_le
    {d : Type*} [Fintype d] [Nonempty d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    {τ : ℝ} (hτ : 0 < τ)
    (atlas : ℕ → ProbabilityMeasure (UnitAddTorus d))
    (hatlas : ∀ r,
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 (atlas r)))
    (k : ProjectiveCharacter d)
    (hactive :
      SpectralCharacterActive (spectralTaylorJet series) k)
    (r m : ℕ) :
    PhaseReplicaCharacterVisibleAt atlas r m k ↔
      spectralCharacterBirthOrder
          (spectralTaylorJet series) k hactive ≤ r ∧
        projectiveCharacterReplicaHeight k ≤ m := by
  classical
  constructor
  · intro hvisible
    exact
      (phaseReplicaCharacterVisible_exactCorner
        energy series henergy omega hreal hτ
        atlas hatlas k hactive).2 r m hvisible
  · rintro ⟨hbirth, hheight⟩
    constructor
    · exact
        (finiteAnalyticPhaseLaw_characterUnlocked_iff_birthOrder_le
          energy series henergy omega hreal hτ r
          (atlas r) (hatlas r) k hactive).mpr hbirth
    · exact
        spectralCharacterReplicaRealizes_of_balanced_of_positiveMass_le
          (projectiveCharacter_spectralCharacterBalanced k)
          hheight

/-- **Faithful fidelity-moment visibility cone.** With positive weight on
every spectral branch, an active character has a nonzero coefficient in the
`m`th survival-fidelity moment at temporal order `r` exactly northeast of
its birth/replica corner.  This is coefficient occurrence in the actual
multinomial observable, not only abstract multiplicity realizability. -/
theorem fidelityMomentCharacterVisible_iff_corner_le
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    {τ : ℝ} (hτ : 0 < τ)
    (atlas : ℕ → ProbabilityMeasure (UnitAddTorus d))
    (hatlas : ∀ r,
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 (atlas r)))
    (weight : d → ℝ) (hweight : ∀ i, 0 < weight i)
    (k : ProjectiveCharacter d)
    (hactive :
      SpectralCharacterActive (spectralTaylorJet series) k)
    (r m : ℕ) :
    FidelityMomentCharacterVisibleAt atlas weight r m k ↔
      spectralCharacterBirthOrder
          (spectralTaylorJet series) k hactive ≤ r ∧
        projectiveCharacterReplicaHeight k ≤ m := by
  constructor
  · rintro ⟨hunlocked, hcoefficient⟩
    constructor
    · exact
        (finiteAnalyticPhaseLaw_characterUnlocked_iff_birthOrder_le
          energy series henergy omega hreal hτ r
          (atlas r) (hatlas r) k hactive).mp hunlocked
    · exact
        (fidelityReplicaCharacterCoefficient_pos_iff_positiveMass_le
          hweight (projectiveCharacter_spectralCharacterBalanced k)
          m).mp hcoefficient
  · rintro ⟨hbirth, hheight⟩
    constructor
    · exact
        (finiteAnalyticPhaseLaw_characterUnlocked_iff_birthOrder_le
          energy series henergy omega hreal hτ r
          (atlas r) (hatlas r) k hactive).mpr hbirth
    · exact
        (fidelityReplicaCharacterCoefficient_pos_iff_positiveMass_le
          hweight (projectiveCharacter_spectralCharacterBalanced k)
          m).mpr hheight

namespace FiniteLocalInteractionFamily

/-- **Local space--time--replica visibility cone.** For every active local
site-Möbius relation, weighted connected-spanning geometry bounds its exact
temporal birth from below.  The relation is visible at its birth horizon
and exact minimum replica height, while every time/replica detector capable
of seeing it lies above the local spanning cost and its replica height.

The spatial, temporal, and recurrence statements concern one literal
projective phase character. -/
theorem exists_localSiteMobiusPhaseReplicaVisibilityCone
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)] [∀ v, Nonempty (A v)]
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
    (birthLower : ℕ)
    (hbirth :
      WeightedObserverSteinerLowerBound
        L sites weight birthLower)
    (hactive :
      SpectralCharacterActive
        (L.weightedInteractionShiftSpectralJet
          onsite hinj weight hpos z)
        (siteMobiusProjectiveCharacter
          x alternative sites hsites))
    {τ : ℝ} (hτ : 0 < τ) :
    let k :=
      siteMobiusProjectiveCharacter
        x alternative sites hsites
    let birth :=
      spectralCharacterBirthOrder
        (L.weightedInteractionShiftSpectralJet
          onsite hinj weight hpos z) k hactive
    let height := projectiveCharacterReplicaHeight k
    ∃ atlas :
        ℕ → ProbabilityMeasure
          (UnitAddTorus (∀ v, A v)),
      (∀ r,
        Tendsto
          (fun g =>
            finiteTorusPhaseProbabilityMeasure
              (L.weightedInteractionShiftFrequency
                onsite hinj weight z g)
              (τ / g ^ r))
          (𝓝[>] 0) (𝓝 (atlas r))) ∧
      birthLower ≤ birth ∧
      PhaseReplicaCharacterVisibleAt
        atlas birth height k ∧
      ∀ r m,
        PhaseReplicaCharacterVisibleAt atlas r m k →
          birthLower ≤ r ∧ height ≤ m := by
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
  let k : ProjectiveCharacter (∀ v, A v) :=
    siteMobiusProjectiveCharacter
      x alternative sites hsites
  change
    SpectralCharacterActive
      (spectralTaylorJet series) k at hactive
  obtain ⟨atlas, hatlas, _⟩ :=
    existsUnique_observerTimeFourierValuationAtlas
      energy series
      (fun config =>
        L.weightedInteractionShiftSeries_spec
          onsite hinj weight hpos z config)
      omega
      (fun config =>
        L.weightedInteractionShiftBranch_eventually_real
          hL onsite hinj weight hpos z config)
      hτ
  have hlower :
      birthLower ≤
        spectralCharacterBirthOrder
          (spectralTaylorJet series) k hactive := by
    apply
      (mem_spectralConstraintFiltration_iff_le_birthOrder
        hactive birthLower).mp
    exact
      L.siteMobiusProjectiveCharacter_mem_weightedConstraint
        onsite hinj x alternative sites hsites
        weight hpos z birthLower hbirth
  have hcorner :=
    phaseReplicaCharacterVisible_exactCorner
      energy series
      (fun config =>
        L.weightedInteractionShiftSeries_spec
          onsite hinj weight hpos z config)
      omega
      (fun config =>
        L.weightedInteractionShiftBranch_eventually_real
          hL onsite hinj weight hpos z config)
      hτ atlas (fun r => (hatlas r).1) k hactive
  dsimp only at hcorner
  refine
    ⟨atlas, (fun r => (hatlas r).1), hlower,
      hcorner.1, ?_⟩
  intro r m hvisible
  have hb := hcorner.2 r m hvisible
  exact ⟨hlower.trans hb.1, hb.2⟩

/-- **Explicit local space--time--replica law.** If every selected site is
genuinely changed, a site-Möbius relation supported on `s` sites has exact
minimum replica height `2^(s-1)`.  Local connected-spanning geometry still
bounds its temporal birth from below, and the resulting explicit corner is
attained. -/
theorem exists_localSiteMobiusExplicitVisibilityCone
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)] [∀ v, Nonempty (A v)]
    (L : FiniteLocalInteractionFamily V E A)
    (hL : HermitianInteractionFamily L)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (hsites : sites.Nonempty)
    (hdistinct : ∀ v ∈ sites, alternative v ≠ x v)
    (weight : E → ℕ) (hpos : ∀ e, 0 < weight e)
    (z : E → ℝ)
    (birthLower : ℕ)
    (hbirth :
      WeightedObserverSteinerLowerBound
        L sites weight birthLower)
    (hactive :
      SpectralCharacterActive
        (L.weightedInteractionShiftSpectralJet
          onsite hinj weight hpos z)
        (siteMobiusProjectiveCharacter
          x alternative sites hsites))
    {τ : ℝ} (hτ : 0 < τ) :
    let k :=
      siteMobiusProjectiveCharacter
        x alternative sites hsites
    let birth :=
      spectralCharacterBirthOrder
        (L.weightedInteractionShiftSpectralJet
          onsite hinj weight hpos z) k hactive
    let height := 2 ^ (sites.card - 1)
    ∃ atlas :
        ℕ → ProbabilityMeasure
          (UnitAddTorus (∀ v, A v)),
      (∀ r,
        Tendsto
          (fun g =>
            finiteTorusPhaseProbabilityMeasure
              (L.weightedInteractionShiftFrequency
                onsite hinj weight z g)
              (τ / g ^ r))
          (𝓝[>] 0) (𝓝 (atlas r))) ∧
      birthLower ≤ birth ∧
      PhaseReplicaCharacterVisibleAt
        atlas birth height k ∧
      ∀ r m,
        PhaseReplicaCharacterVisibleAt atlas r m k →
          birthLower ≤ r ∧ height ≤ m := by
  dsimp only
  let k : ProjectiveCharacter (∀ v, A v) :=
    siteMobiusProjectiveCharacter
      x alternative sites hsites
  have hreplica :=
    siteMobiusProjectiveCharacter_minimumReplica
      x alternative sites hsites hdistinct
  have hbalanced :
      SpectralCharacterBalanced (fun config => k.1 config) :=
    projectiveCharacter_spectralCharacterBalanced k
  have hheight_le :
      projectiveCharacterReplicaHeight k ≤
        2 ^ (sites.card - 1) := by
    exact
      spectralCharacterPositiveMass_le_of_replicaRealizes
        hreplica.1
  have hheight_ge :
      2 ^ (sites.card - 1) ≤
        projectiveCharacterReplicaHeight k := by
    exact
      hreplica.2
        (projectiveCharacterReplicaHeight k)
        (spectralCharacterReplicaRealizes_positiveMass_of_balanced
          hbalanced)
  have hheight :
      projectiveCharacterReplicaHeight k =
        2 ^ (sites.card - 1) :=
    le_antisymm hheight_le hheight_ge
  obtain ⟨atlas, hatlas, hlower, hcorner, hminimal⟩ :=
    L.exists_localSiteMobiusPhaseReplicaVisibilityCone
      hL onsite hinj x alternative sites hsites
      weight hpos z birthLower hbirth hactive hτ
  refine ⟨atlas, hatlas, hlower, ?_, ?_⟩
  · simpa [k, hheight] using hcorner
  · intro r m hvisible
    have h := hminimal r m hvisible
    simpa [k, hheight] using h

/-- **Operational local visibility cone.** For a full-support survival
state, the explicit local corner is attained by a strictly positive
coefficient in the actual fidelity moment.  Every lower temporal order is
locked and every lower fidelity order has zero coefficient. -/
theorem exists_localSiteMobiusExplicitFidelityVisibilityCone
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)] [∀ v, Nonempty (A v)]
    (L : FiniteLocalInteractionFamily V E A)
    (hL : HermitianInteractionFamily L)
    (onsite : ∀ v, A v → ℝ)
    (hinj :
      Function.Injective
        (onsiteProductEnergy (complexOnsite onsite)))
    (x alternative : ∀ v, A v) (sites : Finset V)
    (hsites : sites.Nonempty)
    (hdistinct : ∀ v ∈ sites, alternative v ≠ x v)
    (interactionWeight : E → ℕ)
    (hpos : ∀ e, 0 < interactionWeight e)
    (z : E → ℝ)
    (birthLower : ℕ)
    (hbirth :
      WeightedObserverSteinerLowerBound
        L sites interactionWeight birthLower)
    (hactive :
      SpectralCharacterActive
        (L.weightedInteractionShiftSpectralJet
          onsite hinj interactionWeight hpos z)
        (siteMobiusProjectiveCharacter
          x alternative sites hsites))
    (spectralWeight : (∀ v, A v) → ℝ)
    (hspectralWeight : ∀ config, 0 < spectralWeight config)
    {τ : ℝ} (hτ : 0 < τ) :
    let k :=
      siteMobiusProjectiveCharacter
        x alternative sites hsites
    let birth :=
      spectralCharacterBirthOrder
        (L.weightedInteractionShiftSpectralJet
          onsite hinj interactionWeight hpos z) k hactive
    let height := 2 ^ (sites.card - 1)
    ∃ atlas :
        ℕ → ProbabilityMeasure
          (UnitAddTorus (∀ v, A v)),
      (∀ r,
        Tendsto
          (fun g =>
            finiteTorusPhaseProbabilityMeasure
              (L.weightedInteractionShiftFrequency
                onsite hinj interactionWeight z g)
              (τ / g ^ r))
          (𝓝[>] 0) (𝓝 (atlas r))) ∧
      birthLower ≤ birth ∧
      FidelityMomentCharacterVisibleAt
        atlas spectralWeight birth height k ∧
      ∀ r m,
        FidelityMomentCharacterVisibleAt
            atlas spectralWeight r m k →
          birthLower ≤ r ∧ height ≤ m := by
  dsimp only
  obtain ⟨atlas, hatlas, hlower, hcorner, hminimal⟩ :=
    L.exists_localSiteMobiusExplicitVisibilityCone
      hL onsite hinj x alternative sites hsites hdistinct
      interactionWeight hpos z birthLower hbirth hactive hτ
  refine ⟨atlas, hatlas, hlower, ?_, ?_⟩
  · exact
      ⟨hcorner.1,
        (fidelityReplicaCharacterCoefficient_pos_iff_realizes
          hspectralWeight _ _).mpr hcorner.2⟩
  · intro r m hvisible
    apply hminimal r m
    exact
      ⟨hvisible.1,
        (fidelityReplicaCharacterCoefficient_pos_iff_realizes
          hspectralWeight _ _).mp hvisible.2⟩

end FiniteLocalInteractionFamily

end

end GaloisForLFunctions.HTGeometry
