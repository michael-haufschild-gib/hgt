import GaloisForLFunctions.HTGeometry.HermitianCoupledAllVertexMaximalLeafExtension
import GaloisForLFunctions.HTGeometry.ChartProbeFamilyReduction

/-!
# Recursive Hermitian observer-family leaf extension

The inductive invariant is a maximally projective real spectrum together
with, at every observer site, a finite Hermitian matrix family whose union
transition support is connected and nonbipartite.  One observer family can
be compressed to the next attachment channel, and the coupled extension
returns the same invariant on the enlarged spectral coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe uI uρ uS

/-- A finite Hermitian observer family is good when its union transition
support is connected and nonbipartite at every indexed observer. -/
def HermitianObserverFamilyGood
    {α S : Type*} {η : S → Type*}
    (transition : ∀ s, η s → Matrix α α ℂ) : Prop :=
  ∀ s,
    (∀ i, (transition s i).IsHermitian) ∧
    (transitionFamilySupportGraph (transition s)).Preconnected ∧
    ¬ (transitionFamilySupportGraph (transition s)).IsBipartite

/-- Observer labels after adjoining one new leaf. -/
abbrev LeafExtendedObserver (S : Type uS) : Type uS :=
  Sum S Unit

/-- Probe labels naturally returned at each observer after one leaf
extension. -/
abbrev LeafExtendedProbeIndex
    {I : Type uI} {ρ : Type uρ} {S : Type uS}
    (G : S → SimpleGraph I)
    (attachment : Matrix I I ℂ)
    (anchor : ρ) :
    LeafExtendedObserver S → Type (max uI uρ)
  | Sum.inl s =>
      Sum (GraphEdge (G s)) (NonanchorLayer anchor)
  | Sum.inr _ =>
      Sum (TransitionSupportEdge attachment × ρ)
        (NonanchorLayer anchor)

noncomputable instance leafExtendedProbeIndexFintype
    {I ρ S : Type*} [Fintype I] [Fintype ρ]
    (G : S → SimpleGraph I)
    (attachment : Matrix I I ℂ)
    (anchor : ρ)
    (s : LeafExtendedObserver S) :
    Fintype (LeafExtendedProbeIndex G attachment anchor s) := by
  cases s with
  | inl s =>
      letI : Fintype (GraphEdge (G s)) :=
        Fintype.ofInjective Subtype.val Subtype.val_injective
      letI : Fintype (NonanchorLayer anchor) :=
        Fintype.ofInjective Subtype.val Subtype.val_injective
      exact inferInstance
  | inr u =>
      letI : Fintype (TransitionSupportEdge attachment) :=
        Fintype.ofInjective Subtype.val Subtype.val_injective
      letI : Fintype (NonanchorLayer anchor) :=
        Fintype.ofInjective Subtype.val Subtype.val_injective
      exact inferInstance

noncomputable instance leafExtendedProbeIndexDecidableEq
    {I ρ S : Type*} [Fintype I] [Fintype ρ]
    (G : S → SimpleGraph I)
    (attachment : Matrix I I ℂ)
    (anchor : ρ)
    (s : LeafExtendedObserver S) :
    DecidableEq (LeafExtendedProbeIndex G attachment anchor s) :=
  Classical.decEq _

/-- Spectral-coordinate observer matrices returned by the coupled
extension, with old and new observers packaged in one dependent family. -/
abbrev leafExtendedProbeMatrixFamily
    {I : Type uI} {ρ : Type uρ} {S : Type uS}
    [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (G : S → SimpleGraph I)
    (anchor : ρ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (oldProbe :
      ∀ s,
        Sum (GraphEdge (G s)) (NonanchorLayer anchor) →
          Matrix I I ℂ)
    (newProbe :
      Sum (TransitionSupportEdge attachment × ρ)
          (NonanchorLayer anchor) →
        Matrix ρ ρ ℂ)
    (p : (ρ → ℂ) × Matrix ρ ρ ℂ) :
    ∀ s : LeafExtendedObserver S,
      LeafExtendedProbeIndex G attachment anchor s →
        Matrix (I × ρ) (I × ρ) ℂ
  | Sum.inl s =>
      C.oldProbeMatrixFamily
        energy shift attachment (oldProbe s) p
  | Sum.inr _ =>
      C.newProbeMatrixFamily
        energy shift attachment newProbe p

/-- A connected, nonbipartite finite Hermitian family contains one
Hermitian real combination whose transition graph is still connected and
nonbipartite. -/
theorem exists_hermitianTransition_good_of_family_good
    {α η : Type*} [Fintype α] [Fintype η]
    [DecidableEq α] [DecidableEq η]
    (transition : η → Matrix α α ℂ)
    (hHermitian : ∀ i, (transition i).IsHermitian)
    (hconnected :
      (transitionFamilySupportGraph transition).Preconnected)
    (hnonbipartite :
      ¬ (transitionFamilySupportGraph transition).IsBipartite) :
    ∃ p : η → ℝ,
      let A := realMatrixFamilyCombination transition p
      A.IsHermitian ∧
      (transitionFamilySupportGraph transition ≤
        transitionSupportGraph A) ∧
      (transitionSupportGraph A).Preconnected ∧
      ¬ (transitionSupportGraph A).IsBipartite := by
  obtain ⟨p, hpHermitian, hpGraph⟩ :=
    exists_hermitianTransition_familyGraph_le
      transition hHermitian
  refine ⟨p, hpHermitian, hpGraph,
    hconnected.mono hpGraph, ?_⟩
  intro hA
  exact hnonbipartite (hA.mono_left hpGraph)

/-- **Recursive observer-family extension law.**  Let a finite spectrum be
maximally projective and let every observer carry a finite Hermitian family
with connected, nonbipartite union support.  Choose any current observer as
the attachment site.  Then every finite new local alphabet of size at
least two admits one Hermitian leaf extension whose enlarged labeled real
spectrum is maximally projective and whose old observers together with the
new observer again form a good Hermitian observer family.

The output has exactly the same invariant as the input, so the theorem
iterates without an entrywise-reality or transpose-symmetry hypothesis. -/
theorem
    exists_maximallyProjective_goodObserverFamily_leafExtension
    {I ρ S : Type*} {η : S → Type*}
    [Fintype I] [Fintype ρ] [Fintype S]
    [DecidableEq I] [DecidableEq ρ] [DecidableEq S]
    [Nonempty I] [Nontrivial I]
    [∀ s, Fintype (η s)] [∀ s, DecidableEq (η s)]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (transition : ∀ s, η s → Matrix I I ℂ)
    (hfamily : HermitianObserverFamilyGood transition)
    (root : S)
    (anchor other : ρ) (hother : other ≠ anchor)
    (hcard : 2 ≤ Fintype.card ρ) :
    ∃ attachment : Matrix I I ℂ,
      ∃ n : ℕ,
        let shift : ρ → ℂ :=
          fun r => (codedIntegerLayerShift anchor n r : ℂ)
        let G : S → SimpleGraph I :=
          fun s => transitionFamilySupportGraph (transition s)
        ∃ C : LocalExtensionEigenbranchChart
            (fun i => (energy i : ℂ)) shift attachment,
          ∃ oldProbe :
              ∀ s : S,
                Sum (GraphEdge (G s)) (NonanchorLayer anchor) →
                  Matrix I I ℂ,
            ∃ newProbe :
                Sum (TransitionSupportEdge attachment × ρ)
                    (NonanchorLayer anchor) →
                  Matrix ρ ρ ℂ,
              ∃ q :
                  Fin (localExtensionSliceParameterCount ρ) → ℝ,
                let p :=
                  realLocalExtensionParameter
                    (localExtensionSliceParameter q)
                let nextEnergy :=
                  C.realBranchEnergy
                    (fun i => (energy i : ℂ))
                    shift attachment p
                let nextTransition :=
                  leafExtendedProbeMatrixFamily
                    (fun i => (energy i : ℂ))
                    shift attachment G anchor C
                    oldProbe newProbe p
                MaximallyProjectiveEnergy nextEnergy ∧
                  HermitianObserverFamilyGood nextTransition := by
  classical
  let G : S → SimpleGraph I :=
    fun s => transitionFamilySupportGraph (transition s)
  obtain ⟨attachmentCoefficient, hattachmentHermitian,
      hfamilyLe, hattachmentConnected,
      hattachmentNonbipartite⟩ :=
    exists_hermitianTransition_good_of_family_good
      (transition root) (hfamily root).1
      (hfamily root).2.1 (hfamily root).2.2
  let attachment : Matrix I I ℂ :=
    realMatrixFamilyCombination
      (transition root) attachmentCoefficient
  let baseIndex :
      ∀ s : S, GraphEdge (G s) → η s :=
    fun s e => Classical.choose e.2
  let baseProbe :
      ∀ s : S, GraphEdge (G s) → Matrix I I ℂ :=
    fun s e => transition s (baseIndex s e)
  have hbaseProbeHermitian :
      ∀ (s : S) (e : GraphEdge (G s)),
        (baseProbe s e).IsHermitian := by
    intro s e
    exact (hfamily s).1 (baseIndex s e)
  have hbaseProbeEntry :
      ∀ (s : S) (e : GraphEdge (G s)),
        baseProbe s e e.1.1 e.1.2 ≠ 0 := by
    intro s e
    have hedge :
        (transitionSupportGraph
          (transition s (baseIndex s e))).Adj
            e.1.1 e.1.2 :=
      Classical.choose_spec e.2
    exact
      (transitionSupportGraph_adj_iff_entry_ne_zero_of_isHermitian
        _ ((hfamily s).1 (baseIndex s e))
        e.1.1 e.1.2).mp hedge |>.2
  let middle : I :=
    Classical.choice (inferInstance : Nonempty I)
  have hattachmentNeighbor :
      ((transitionSupportGraph attachment).neighborSet middle).Nonempty := by
    exact ((transitionSupportGraph attachment).neighborSet_nonempty).mpr
      (hattachmentConnected.not_isIsolated middle)
  obtain ⟨source, hsourceAdj⟩ :=
    SimpleGraph.nonempty_neighborSet.mp hattachmentNeighbor
  have hobserverNeighbor :
      ∀ s : S, ∃ target,
        (G s).Adj middle target := by
    intro s
    apply SimpleGraph.nonempty_neighborSet.mp
    exact ((G s).neighborSet_nonempty).mpr
      ((hfamily s).2.1.not_isIsolated middle)
  choose target htargetAdj using hobserverNeighbor
  have hobserverProbe :
      ∀ s : S, ∃ i,
        (transitionSupportGraph (transition s i)).Adj
          middle (target s) := by
    intro s
    exact htargetAdj s
  choose crossIndex hcrossIndexAdj using hobserverProbe
  let crossSource :
      ∀ _s : S, NonanchorLayer anchor → I :=
    fun _ _ => source
  let crossMiddle :
      ∀ _s : S, NonanchorLayer anchor → I :=
    fun _ _ => middle
  let crossTarget :
      ∀ s : S, NonanchorLayer anchor → I :=
    fun s _ => target s
  let crossProbe :
      ∀ s : S, NonanchorLayer anchor → Matrix I I ℂ :=
    fun s _ => transition s (crossIndex s)
  have hcrossProbeHermitian :
      ∀ (s : S) (q : NonanchorLayer anchor),
        (crossProbe s q).IsHermitian := by
    intro s q
    exact (hfamily s).1 (crossIndex s)
  have hsourceMiddle :
      ∀ (s : S) (q : NonanchorLayer anchor),
        crossSource s q ≠ crossMiddle s q := by
    intro s q
    exact hsourceAdj.ne.symm
  have hmiddleTarget :
      ∀ (s : S) (q : NonanchorLayer anchor),
        crossMiddle s q ≠ crossTarget s q := by
    intro s q
    exact (htargetAdj s).ne
  have hattachmentEntry :
      ∀ (s : S) (q : NonanchorLayer anchor),
        attachment (crossSource s q) (crossMiddle s q) ≠ 0 := by
    intro s q
    exact
      (transitionSupportGraph_adj_iff_entry_ne_zero_of_isHermitian
        attachment hattachmentHermitian source middle).mp
          hsourceAdj.symm |>.2
  have hcrossProbeEntry :
      ∀ (s : S) (q : NonanchorLayer anchor),
        crossProbe s q (crossMiddle s q) (crossTarget s q) ≠ 0 := by
    intro s q
    exact
      (transitionSupportGraph_adj_iff_entry_ne_zero_of_isHermitian
        _ ((hfamily s).1 (crossIndex s))
        middle (target s)).mp (hcrossIndexAdj s) |>.2
  obtain ⟨n, C, oldProbe, newProbe, q,
      holdProbeHermitian, _holdProbeSource, hnewProbeHermitian,
      hqMaximal, hqGood⟩ :=
    exists_allVertexGood_maximallyProjective_leafExtension_of_isHermitian
      energy hmax anchor other hother hcard
      attachment hattachmentHermitian
      hattachmentConnected hattachmentNonbipartite
      G (fun s => (hfamily s).2.1)
      (fun s => (hfamily s).2.2)
      baseProbe hbaseProbeHermitian hbaseProbeEntry
      crossSource crossMiddle crossTarget crossProbe
      hcrossProbeHermitian hsourceMiddle hmiddleTarget
      hattachmentEntry hcrossProbeEntry
  let shift : ρ → ℂ :=
    fun r => (codedIntegerLayerShift anchor n r : ℂ)
  let p : (ρ → ℂ) × Matrix ρ ρ ℂ :=
    realLocalExtensionParameter (localExtensionSliceParameter q)
  have hH :
      (localExtensionMatrix
        (fun i => (energy i : ℂ)) p.1 attachment p.2).IsHermitian := by
    simpa [p, hermitianLocalExtensionSliceMatrix] using
      hermitianLocalExtensionSliceMatrix_isHermitian
        energy attachment hattachmentHermitian q
  have hnextMaximal :
      MaximallyProjectiveEnergy
        (C.realBranchEnergy
          (fun i => (energy i : ℂ))
          shift attachment p) :=
    C.realBranchEnergy_maximallyProjective
      (fun i => (energy i : ℂ))
      shift attachment p hqGood.1 hH hqMaximal
  let nextTransition :=
    leafExtendedProbeMatrixFamily
      (fun i => (energy i : ℂ))
      shift attachment G anchor C
      oldProbe newProbe p
  have hnextFamily :
      HermitianObserverFamilyGood nextTransition := by
    intro s
    cases s with
    | inl s =>
        refine ⟨?_, ?_, ?_⟩
        · intro i
          exact C.oldProbeMatrixFamily_isHermitian
            (fun i => (energy i : ℂ))
            shift attachment (oldProbe s)
            (holdProbeHermitian s) p i
        · rw [
            transitionFamilySupportGraph_oldProbeMatrixFamily
              (fun i => (energy i : ℂ))
              shift attachment C (oldProbe s)
              (holdProbeHermitian s) p]
          exact hqGood.2.1 s |>.1
        · rw [
            transitionFamilySupportGraph_oldProbeMatrixFamily
              (fun i => (energy i : ℂ))
              shift attachment C (oldProbe s)
              (holdProbeHermitian s) p]
          exact hqGood.2.1 s |>.2
    | inr u =>
        refine ⟨?_, ?_, ?_⟩
        · intro i
          exact C.newProbeMatrixFamily_isHermitian
            (fun i => (energy i : ℂ))
            shift attachment newProbe
            hnewProbeHermitian p i
        · rw [
            transitionFamilySupportGraph_newProbeMatrixFamily
              (fun i => (energy i : ℂ))
              shift attachment C newProbe
              hnewProbeHermitian p]
          exact hqGood.2.2.1
        · rw [
            transitionFamilySupportGraph_newProbeMatrixFamily
              (fun i => (energy i : ℂ))
              shift attachment C newProbe
              hnewProbeHermitian p]
          exact hqGood.2.2.2
  exact ⟨attachment, n, C, oldProbe, newProbe, q,
    hnextMaximal, hnextFamily⟩

end

end GaloisForLFunctions.HTGeometry
