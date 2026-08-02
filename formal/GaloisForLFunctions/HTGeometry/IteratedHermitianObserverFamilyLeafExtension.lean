import GaloisForLFunctions.HTGeometry.UnitaryHermitianObserverFamilyLeafExtension
import GaloisForLFunctions.HTGeometry.FiniteEntropyPlateauFutureLaw

/-!
# Arbitrarily long Hermitian observer-family growth

The recursive leaf-extension invariant is packaged as a finite spectral
system and iterated through any prescribed finite list of local
dimensions.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology

universe u

/-- A finite spectral system carrying maximal projective rank and one good
finite Hermitian observer family at every observer label. -/
structure GoodObserverSpectralSystem where
  State : Type u
  Observer : Type u
  Probe : Observer → Type u
  [stateFintype : Fintype State]
  [stateDecidableEq : DecidableEq State]
  [stateNonempty : Nonempty State]
  [stateNontrivial : Nontrivial State]
  [observerFintype : Fintype Observer]
  [observerDecidableEq : DecidableEq Observer]
  [observerNonempty : Nonempty Observer]
  [probeFintype : ∀ s, Fintype (Probe s)]
  [probeDecidableEq : ∀ s, DecidableEq (Probe s)]
  energy : State → ℝ
  energy_maximallyProjective :
    MaximallyProjectiveEnergy energy
  transition :
    ∀ s, Probe s → Matrix State State ℂ
  observerFamily_good :
    HermitianObserverFamilyGood transition

/-- Number of spectral states in a packaged system. -/
def GoodObserverSpectralSystem.stateCard
    (X : GoodObserverSpectralSystem) : ℕ :=
  @Fintype.card X.State X.stateFintype

/-- Number of indexed observers in a packaged system. -/
def GoodObserverSpectralSystem.observerCard
    (X : GoodObserverSpectralSystem) : ℕ :=
  @Fintype.card X.Observer X.observerFintype

/-- Full finite-entropy recurrence conclusion carried by a packaged
maximally projective spectrum: simple spectrum, entropy-floor
microcanonical plateau, every replica permutation floor, and Haar
equidistribution of every projective phase packet. -/
def GoodObserverSpectralSystem.HasFiniteEntropyPlateauFuture
    (X : GoodObserverSpectralSystem) : Prop :=
  letI : Fintype X.State := X.stateFintype
  letI : DecidableEq X.State := X.stateDecidableEq
  letI : Nonempty X.State := X.stateNonempty
  Function.Injective X.energy ∧
    Tendsto
      (finiteSpectralSurvivalFidelityMean
        (microcanonicalWeight X.State) X.energy 1)
      atTop
      (𝓝 ((Fintype.card X.State : ℝ)⁻¹ : ℂ)) ∧
    (∀ n : ℕ,
      Tendsto
        (finiteSpectralSurvivalFidelityMean
          (microcanonicalWeight X.State) X.energy n)
        atTop
        (𝓝
          (fidelityReplicaPermutationFloor
            (microcanonicalWeight X.State) n : ℂ))) ∧
    ∀ reference : X.State,
      Tendsto
        (finiteTorusPhaseProbabilityMeasure
          (projectiveFrequency X.energy reference))
        atTop
        (𝓝
          (finiteTorusHaarProbabilityMeasure
            {i : X.State // i ≠ reference}))

/-- Every packaged good observer spectral system already satisfies the
complete finite-entropy plateau--future law. -/
theorem GoodObserverSpectralSystem.hasFiniteEntropyPlateauFuture
    (X : GoodObserverSpectralSystem) :
    X.HasFiniteEntropyPlateauFuture := by
  letI : Fintype X.State := X.stateFintype
  letI : DecidableEq X.State := X.stateDecidableEq
  letI : Nonempty X.State := X.stateNonempty
  simpa [GoodObserverSpectralSystem.HasFiniteEntropyPlateauFuture] using
    (finiteEntropyPlateauFutureLaw
      X.energy_maximallyProjective)

/-- **Closure of the packaged invariant under any finite leaf.**  A good
observer spectral system can be enlarged at a chosen observer by any
finite local alphabet of cardinality at least two.  Spectral-state count
is multiplied by the local dimension, observer count increases by one,
and maximal projective rank plus all-observer goodness are retained. -/
theorem GoodObserverSpectralSystem.exists_leafExtension
    (X : GoodObserverSpectralSystem.{u})
    (root : X.Observer)
    (ρ : Type u) [Fintype ρ] [DecidableEq ρ]
    (anchor other : ρ) (hother : other ≠ anchor)
    (hcard : 2 ≤ Fintype.card ρ) :
    ∃ Y : GoodObserverSpectralSystem.{u},
      Y.stateCard = X.stateCard * Fintype.card ρ ∧
      Y.observerCard = X.observerCard + 1 := by
  letI : Fintype X.State := X.stateFintype
  letI : DecidableEq X.State := X.stateDecidableEq
  letI : Nonempty X.State := X.stateNonempty
  letI : Nontrivial X.State := X.stateNontrivial
  letI : Fintype X.Observer := X.observerFintype
  letI : DecidableEq X.Observer := X.observerDecidableEq
  letI : Nonempty X.Observer := X.observerNonempty
  letI : ∀ s, Fintype (X.Probe s) := X.probeFintype
  letI : ∀ s, DecidableEq (X.Probe s) := X.probeDecidableEq
  letI : Nontrivial ρ :=
    Fintype.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨attachment, _hattachmentOrigin, n, C, oldProbe,
      _holdProbeOrigin, newProbe, q,
      hH, e, he, hdiagonal, hnextMaximal, hnextGood⟩ :=
    exists_maximallyProjective_unitaryGoodObserverFamily_leafExtension
      X.energy X.energy_maximallyProjective
      X.transition X.observerFamily_good root
      anchor other hother hcard
  let shift : ρ → ℂ :=
    fun r => (codedIntegerLayerShift anchor n r : ℂ)
  let G : X.Observer → SimpleGraph X.State :=
    fun s => transitionFamilySupportGraph (X.transition s)
  let p : (ρ → ℂ) × Matrix ρ ρ ℂ :=
    realLocalExtensionParameter (localExtensionSliceParameter q)
  let nextEnergy : X.State × ρ → ℝ :=
    C.realBranchEnergy
      (fun i => (X.energy i : ℂ))
      shift attachment p
  let nextTransition :
      ∀ s : LeafExtendedObserver X.Observer,
        LeafExtendedProbeIndex G attachment anchor s →
          Matrix (X.State × ρ) (X.State × ρ) ℂ :=
    unitaryLeafExtendedProbeMatrixFamily
      G anchor C oldProbe newProbe hH e
  let Y : GoodObserverSpectralSystem.{u} :=
    { State := X.State × ρ
      Observer := LeafExtendedObserver X.Observer
      Probe := LeafExtendedProbeIndex G attachment anchor
      stateFintype := inferInstance
      stateDecidableEq := inferInstance
      stateNonempty := inferInstance
      stateNontrivial := inferInstance
      observerFintype := inferInstance
      observerDecidableEq := inferInstance
      observerNonempty := inferInstance
      probeFintype :=
        fun s =>
          leafExtendedProbeIndexFintype
            G attachment anchor s
      probeDecidableEq :=
        fun s =>
          leafExtendedProbeIndexDecidableEq
            G attachment anchor s
      energy := nextEnergy
      energy_maximallyProjective := hnextMaximal
      transition := nextTransition
      observerFamily_good := hnextGood }
  refine ⟨Y, ?_, ?_⟩
  · simp [GoodObserverSpectralSystem.stateCard, Y]
  · simp [GoodObserverSpectralSystem.observerCard, Y]

/-- **Arbitrary finite dimension-sequence growth law.**  Starting from any
good observer spectral system, every finite ordered list of local
dimensions at least two can be attached successively.  The final spectral
state count is multiplied by the product of those dimensions, the observer
count grows by the list length, and the packaged maximal-rank/all-observer
invariant still holds. -/
theorem GoodObserverSpectralSystem.exists_leafExtensions_finList
    (X : GoodObserverSpectralSystem.{u})
    (dimension : List ℕ)
    (hdimension :
      ∀ q ∈ dimension, 2 ≤ q) :
    ∃ Y : GoodObserverSpectralSystem.{u},
      Y.stateCard = X.stateCard * dimension.prod ∧
      Y.observerCard = X.observerCard + dimension.length := by
  induction dimension generalizing X with
  | nil =>
      exact ⟨X, by simp, by simp⟩
  | cons q qs ih =>
      have hq : 2 ≤ q :=
        hdimension q (by simp)
      let anchorFin : Fin q :=
        ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩
      let otherFin : Fin q :=
        ⟨1, hq⟩
      have hotherFin : otherFin ≠ anchorFin := by
        intro h
        have := congrArg Fin.val h
        simp [otherFin, anchorFin] at this
      let Local : Type u := ULift.{u} (Fin q)
      let anchor : Local := ULift.up anchorFin
      let other : Local := ULift.up otherFin
      have hother : other ≠ anchor := by
        intro h
        exact hotherFin (ULift.up_injective h)
      obtain ⟨X₁, hX₁state, hX₁observer⟩ :=
        X.exists_leafExtension
          (Classical.choice X.observerNonempty)
          Local anchor other hother (by simpa [Local] using hq)
      have hqs :
          ∀ r ∈ qs, 2 ≤ r := by
        intro r hr
        exact hdimension r (by simp [hr])
      obtain ⟨Y, hYstate, hYobserver⟩ :=
        ih X₁ hqs
      refine ⟨Y, ?_, ?_⟩
      · rw [hYstate, hX₁state]
        have hLocalCard : Fintype.card Local = q := by
          simp [Local]
        rw [hLocalCard]
        simp only [List.prod_cons]
        ac_rfl
      · rw [hYobserver, hX₁observer]
        simp only [List.length_cons]
        omega

/-- **Arbitrarily long all-observer recurrence law.**  Every prescribed
finite sequence of local dimensions at least two admits a successive leaf
growth that retains all-observer Hermitian observability and, at the final
size, obeys the exact entropy-floor plateau, every replica permutation
floor, and full-Haar projective recurrence. -/
theorem GoodObserverSpectralSystem.exists_leafExtensions_finList_with_fullRecurrence
    (X : GoodObserverSpectralSystem.{u})
    (dimension : List ℕ)
    (hdimension :
      ∀ q ∈ dimension, 2 ≤ q) :
    ∃ Y : GoodObserverSpectralSystem.{u},
      Y.stateCard = X.stateCard * dimension.prod ∧
      Y.observerCard = X.observerCard + dimension.length ∧
      Y.HasFiniteEntropyPlateauFuture := by
  obtain ⟨Y, hstate, hobserver⟩ :=
    X.exists_leafExtensions_finList dimension hdimension
  exact ⟨Y, hstate, hobserver,
    Y.hasFiniteEntropyPlateauFuture⟩

end

end GaloisForLFunctions.HTGeometry
