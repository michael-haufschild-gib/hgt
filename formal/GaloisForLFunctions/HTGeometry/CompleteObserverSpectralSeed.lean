import GaloisForLFunctions.HTGeometry.IteratedHermitianObserverFamilyLeafExtension
import GaloisForLFunctions.HTGeometry.WeakInteractionRecurrenceSingularityLaw

/-!
# Complete observer-family spectral seeds

A finite spectral packet of cardinality at least three admits a maximally
projective energy assignment and, at any prescribed finite nonempty set of
observer labels, an explicit finite Hermitian probe family whose union
transition graph is complete.  This supplies a nonempty seed for the
recursive leaf-extension law.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- One oriented label for every edge of the complete graph. -/
abbrev CompleteObserverProbeIndex (I : Type u) :=
  GraphEdge (⊤ : SimpleGraph I)

noncomputable instance completeObserverProbeIndexFintype
    (I : Type u) [Fintype I] :
    Fintype (CompleteObserverProbeIndex I) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance completeObserverProbeIndexDecidableEq
    (I : Type u) :
    DecidableEq (CompleteObserverProbeIndex I) :=
  Classical.decEq _

/-- Explicit Hermitian matrix supported on one complete-graph edge. -/
def completeObserverProbe
    {I : Type u} [DecidableEq I]
    (e : CompleteObserverProbeIndex I) :
    Matrix I I ℂ :=
  hermitianLayerCosineProbe e.1.1 e.1.2

theorem completeObserverProbe_isHermitian
    {I : Type u} [DecidableEq I]
    (e : CompleteObserverProbeIndex I) :
    (completeObserverProbe e).IsHermitian :=
  hermitianLayerCosineProbe_isHermitian e.1.1 e.1.2

/-- The explicit edge-probe family detects every and only off-diagonal
transition, so its union support is the complete graph. -/
theorem transitionFamilySupportGraph_completeObserverProbe
    {I : Type u} [DecidableEq I] :
    transitionFamilySupportGraph
        (completeObserverProbe :
          CompleteObserverProbeIndex I → Matrix I I ℂ) =
      (⊤ : SimpleGraph I) := by
  ext a b
  constructor
  · rintro ⟨e, he⟩
    simpa using he.1
  · intro hab
    have hne : a ≠ b := by
      simpa using hab
    let e : CompleteObserverProbeIndex I :=
      ⟨(a, b), by simpa using hne⟩
    refine ⟨e, ?_⟩
    refine ⟨hne, ?_⟩
    dsimp [e]
    simp [completeObserverProbe, hermitianLayerCosineProbe,
      directedLayerMatrix, hne]

/-- A complete graph on at least three vertices is nonbipartite. -/
theorem completeGraph_not_isBipartite_of_three_le_card
    {I : Type u} [Fintype I]
    (hcard : 3 ≤ Fintype.card I) :
    ¬ (⊤ : SimpleGraph I).IsBipartite := by
  intro h
  have hchromatic :
      (⊤ : SimpleGraph I).chromaticNumber ≤ 2 :=
    SimpleGraph.chromaticNumber_le_two_iff_isBipartite.mpr h
  rw [SimpleGraph.chromaticNumber_top] at hchromatic
  have hcard_le : Fintype.card I ≤ 2 := by
    exact_mod_cast hchromatic
  omega

/-- **Explicit nonempty seed theorem.**  Every finite state carrier with
at least three states and every finite nonempty observer set admit a good
observer spectral system.  Its observer support graph is complete at every
observer and its real energy packet is maximally projective. -/
theorem exists_completeObserverSpectralSystem
    (I S : Type u) [Fintype I] [DecidableEq I]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (hcard : 3 ≤ Fintype.card I) :
    ∃ X : GoodObserverSpectralSystem.{u},
      X.stateCard = Fintype.card I ∧
      X.observerCard = Fintype.card S := by
  letI : Nonempty I :=
    Fintype.card_pos_iff.mp (by omega)
  letI : Nontrivial I :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨energy, henergyMaximal, _hclose⟩ :=
    exists_maximallyProjectiveEnergy_close_fintype
      (fun _ : I => 0) 1 (by norm_num)
  let transition :
      ∀ _s : S,
        CompleteObserverProbeIndex I → Matrix I I ℂ :=
    fun _ => completeObserverProbe
  have hgood :
      HermitianObserverFamilyGood transition := by
    intro s
    refine ⟨?_, ?_, ?_⟩
    · intro e
      exact completeObserverProbe_isHermitian e
    · rw [show transitionFamilySupportGraph (transition s) =
          (⊤ : SimpleGraph I) by
            exact transitionFamilySupportGraph_completeObserverProbe]
      exact SimpleGraph.preconnected_top
    · rw [show transitionFamilySupportGraph (transition s) =
          (⊤ : SimpleGraph I) by
            exact transitionFamilySupportGraph_completeObserverProbe]
      exact completeGraph_not_isBipartite_of_three_le_card hcard
  let X : GoodObserverSpectralSystem.{u} :=
    { State := I
      Observer := S
      Probe := fun _ => CompleteObserverProbeIndex I
      stateFintype := inferInstance
      stateDecidableEq := inferInstance
      stateNonempty := inferInstance
      stateNontrivial := inferInstance
      observerFintype := inferInstance
      observerDecidableEq := inferInstance
      observerNonempty := inferInstance
      probeFintype := fun _ => inferInstance
      probeDecidableEq := fun _ => inferInstance
      energy := energy
      energy_maximallyProjective := henergyMaximal
      transition := transition
      observerFamily_good := hgood }
  exact ⟨X, by simp [GoodObserverSpectralSystem.stateCard, X],
    by simp [GoodObserverSpectralSystem.observerCard, X]⟩

/-- **Unconditional arbitrary-size observer recurrence systems.**  From
any finite seed carrier with at least three states and any finite nonempty
observer set, every prescribed finite list of further local dimensions at
least two is realized by a good Hermitian observer system with the exact
product state count, exact observer count, and full finite-entropy
plateau--future law. -/
theorem exists_completeSeed_leafExtensions_finList_with_fullRecurrence
    (I S : Type u) [Fintype I] [DecidableEq I]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (hcard : 3 ≤ Fintype.card I)
    (dimension : List ℕ)
    (hdimension :
      ∀ q ∈ dimension, 2 ≤ q) :
    ∃ Y : GoodObserverSpectralSystem.{u},
      Y.stateCard = Fintype.card I * dimension.prod ∧
      Y.observerCard = Fintype.card S + dimension.length ∧
      Y.HasFiniteEntropyPlateauFuture := by
  obtain ⟨X, hXstate, hXobserver⟩ :=
    exists_completeObserverSpectralSystem I S hcard
  obtain ⟨Y, hYstate, hYobserver, hYrecurrence⟩ :=
    X.exists_leafExtensions_finList_with_fullRecurrence
      dimension hdimension
  exact ⟨Y, by simpa [hXstate] using hYstate,
    by simpa [hXobserver] using hYobserver,
    hYrecurrence⟩

end

end GaloisForLFunctions.HTGeometry
