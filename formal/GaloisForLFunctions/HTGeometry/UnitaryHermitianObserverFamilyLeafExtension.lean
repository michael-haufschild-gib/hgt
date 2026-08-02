import GaloisForLFunctions.HTGeometry.HermitianObserverFamilyLeafExtension
import GaloisForLFunctions.HTGeometry.UnitaryChartProbeFamilyReduction

/-!
# Exact-unitary recursive observer-family leaf extension

This replaces adjugate congruence coordinates by a genuine orthonormal
eigenbasis.  Returned observer matrices are therefore exact unitary
coordinate representations of the physical old-factor and new-factor
probes, while retaining every support edge used by the analytic proof.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe uI uρ uS

/-- Physical probe family on the enlarged product basis, before spectral
diagonalization. -/
abbrev leafExtendedPhysicalProbeFamily
    {I : Type uI} {ρ : Type uρ} {S : Type uS}
    [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    (G : S → SimpleGraph I)
    (attachment : Matrix I I ℂ)
    (anchor : ρ)
    (oldProbe :
      ∀ s,
        Sum (GraphEdge (G s)) (NonanchorLayer anchor) →
          Matrix I I ℂ)
    (newProbe :
      Sum (TransitionSupportEdge attachment × ρ)
          (NonanchorLayer anchor) →
        Matrix ρ ρ ℂ) :
    ∀ s : LeafExtendedObserver S,
      LeafExtendedProbeIndex G attachment anchor s →
        Matrix (I × ρ) (I × ρ) ℂ
  | Sum.inl s, q =>
      layerMatrixCoupling (oldProbe s q)
        (1 : Matrix ρ ρ ℂ)
  | Sum.inr _, q =>
      layerMatrixCoupling (1 : Matrix I I ℂ)
        (newProbe q)

/-- Exact orthonormal spectral-coordinate matrices of every physical probe
at every old or newly adjoined observer. -/
abbrev unitaryLeafExtendedProbeMatrixFamily
    {I : Type uI} {ρ : Type uρ} {S : Type uS}
    [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    {energy : I → ℂ} {shift : ρ → ℂ}
    {attachment : Matrix I I ℂ}
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
    {p : (ρ → ℂ) × Matrix ρ ρ ℂ}
    (hH :
      (localExtensionMatrix energy p.1 attachment p.2).IsHermitian)
    (e : (I × ρ) ≃ (I × ρ)) :
    ∀ s : LeafExtendedObserver S,
      LeafExtendedProbeIndex G attachment anchor s →
        Matrix (I × ρ) (I × ρ) ℂ :=
  fun s =>
    C.unitaryProbeMatrixFamily hH e
      (leafExtendedPhysicalProbeFamily
        G attachment anchor oldProbe newProbe s)

/-- Every support edge proved using analytic chart representatives survives
simultaneously for all observers in exact unitary coordinates. -/
theorem unitaryLeafExtendedProbeMatrixFamily_good
    {I : Type uI} {ρ : Type uρ} {S : Type uS}
    [Fintype I] [Fintype ρ] [Fintype S]
    [DecidableEq I] [DecidableEq ρ] [DecidableEq S]
    {energy : I → ℂ} {shift : ρ → ℂ}
    {attachment : Matrix I I ℂ}
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
    (holdProbeHermitian : ∀ s q, (oldProbe s q).IsHermitian)
    (hnewProbeHermitian : ∀ q, (newProbe q).IsHermitian)
    (p : (ρ → ℂ) × Matrix ρ ρ ℂ)
    (hp : p ∈ C.U)
    (hH :
      (localExtensionMatrix energy p.1 attachment p.2).IsHermitian)
    (e : (I × ρ) ≃ (I × ρ))
    (he :
      ∀ i,
        C.realBranchEnergy energy shift attachment p i =
          hH.eigenvalues (e i))
    (holdGood :
      ∀ s,
        (oldSystemLocalExtensionChartProbeSupportGraph
          energy shift attachment C (oldProbe s) p).Preconnected ∧
        ¬ (oldSystemLocalExtensionChartProbeSupportGraph
          energy shift attachment C (oldProbe s) p).IsBipartite)
    (hnewGood :
      (newLayerLocalExtensionChartProbeSupportGraph
        energy shift attachment C newProbe p).Preconnected ∧
      ¬ (newLayerLocalExtensionChartProbeSupportGraph
        energy shift attachment C newProbe p).IsBipartite) :
    HermitianObserverFamilyGood
      (unitaryLeafExtendedProbeMatrixFamily
        G anchor C oldProbe newProbe hH e) := by
  intro s
  cases s with
  | inl s =>
      let physicalProbe :=
        fun q =>
          layerMatrixCoupling (oldProbe s q)
            (1 : Matrix ρ ρ ℂ)
      have hphysicalHermitian :
          ∀ q, (physicalProbe q).IsHermitian := by
        intro q
        exact layerMatrixCoupling_isHermitian
          (holdProbeHermitian s q) Matrix.isHermitian_one
      have hle :
          oldSystemLocalExtensionChartProbeSupportGraph
              energy shift attachment C (oldProbe s) p ≤
            transitionFamilySupportGraph
              (C.unitaryProbeMatrixFamily hH e physicalProbe) := by
        rw [← transitionFamilySupportGraph_oldProbeMatrixFamily
          energy shift attachment C (oldProbe s)
          (holdProbeHermitian s) p]
        exact C.transitionFamilySupportGraph_probeMatrix_le_unitary
          energy shift attachment p hp hH e he physicalProbe
      have hle' :
          oldSystemLocalExtensionChartProbeSupportGraph
              energy shift attachment C (oldProbe s) p ≤
            transitionFamilySupportGraph
              (unitaryLeafExtendedProbeMatrixFamily
                G anchor C oldProbe newProbe hH e (Sum.inl s)) := by
        simpa [unitaryLeafExtendedProbeMatrixFamily,
          leafExtendedPhysicalProbeFamily, physicalProbe] using hle
      refine ⟨?_, (holdGood s).1.mono hle', ?_⟩
      · intro q
        exact C.unitaryProbeMatrixFamily_isHermitian
          hH e physicalProbe hphysicalHermitian q
      · intro hbipartite
        exact (holdGood s).2 (hbipartite.mono_left hle')
  | inr u =>
      let physicalProbe :=
        fun q =>
          layerMatrixCoupling (1 : Matrix I I ℂ)
            (newProbe q)
      have hphysicalHermitian :
          ∀ q, (physicalProbe q).IsHermitian := by
        intro q
        exact layerMatrixCoupling_isHermitian
          Matrix.isHermitian_one (hnewProbeHermitian q)
      have hle :
          newLayerLocalExtensionChartProbeSupportGraph
              energy shift attachment C newProbe p ≤
            transitionFamilySupportGraph
              (C.unitaryProbeMatrixFamily hH e physicalProbe) := by
        rw [← transitionFamilySupportGraph_newProbeMatrixFamily
          energy shift attachment C newProbe
          hnewProbeHermitian p]
        exact C.transitionFamilySupportGraph_probeMatrix_le_unitary
          energy shift attachment p hp hH e he physicalProbe
      have hle' :
          newLayerLocalExtensionChartProbeSupportGraph
              energy shift attachment C newProbe p ≤
            transitionFamilySupportGraph
              (unitaryLeafExtendedProbeMatrixFamily
                G anchor C oldProbe newProbe hH e (Sum.inr u)) := by
        simpa [unitaryLeafExtendedProbeMatrixFamily,
          leafExtendedPhysicalProbeFamily, physicalProbe] using hle
      refine ⟨?_, hnewGood.1.mono hle', ?_⟩
      · intro q
        exact C.unitaryProbeMatrixFamily_isHermitian
          hH e physicalProbe hphysicalHermitian q
      · intro hbipartite
        exact hnewGood.2 (hbipartite.mono_left hle')

/-- **Exact-unitary recursive leaf-extension law.**  The recursive invariant
is preserved using the actual orthonormal eigenbasis of the enlarged physical
Hamiltonian.  Hence every returned observer matrix is an exact unitary
coordinate image of a probe acting only on its old or newly adjoined factor,
not a nonunitary congruence surrogate. -/
theorem
    exists_maximallyProjective_unitaryGoodObserverFamily_leafExtension
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
      (∃ coefficient : η root → ℝ,
        attachment =
          realMatrixFamilyCombination
            (transition root) coefficient) ∧
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
            (∀ s p, ∃ i : η s,
              oldProbe s p = transition s i) ∧
            ∃ newProbe :
                Sum (TransitionSupportEdge attachment × ρ)
                    (NonanchorLayer anchor) →
                  Matrix ρ ρ ℂ,
              ∃ q :
                  Fin (localExtensionSliceParameterCount ρ) → ℝ,
                let p :=
                  realLocalExtensionParameter
                    (localExtensionSliceParameter q)
                ∃ hH :
                    (localExtensionMatrix
                      (fun i => (energy i : ℂ))
                      p.1 attachment p.2).IsHermitian,
                  ∃ e : (I × ρ) ≃ (I × ρ),
                    (∀ i,
                      C.realBranchEnergy
                          (fun i => (energy i : ℂ))
                          shift attachment p i =
                        hH.eigenvalues (e i)) ∧
                    localExtensionMatrix
                        (fun i => (energy i : ℂ))
                        p.1 attachment p.2 =
                      C.unitaryEigenvectorMatrix hH e *
                        Matrix.diagonal
                          (fun i =>
                            (C.realBranchEnergy
                              (fun i => (energy i : ℂ))
                              shift attachment p i : ℂ)) *
                        star (C.unitaryEigenvectorMatrix hH e) ∧
                    MaximallyProjectiveEnergy
                      (C.realBranchEnergy
                        (fun i => (energy i : ℂ))
                        shift attachment p) ∧
                    HermitianObserverFamilyGood
                      (unitaryLeafExtendedProbeMatrixFamily
                        G anchor C oldProbe newProbe hH e) := by
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
      holdProbeHermitian, holdProbeSource, hnewProbeHermitian,
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
  have holdProbeOrigin :
      ∀ s p, ∃ i : η s,
        oldProbe s p = transition s i := by
    intro s p
    cases p with
    | inl edge =>
        refine ⟨baseIndex s edge, ?_⟩
        rw [holdProbeSource]
        rfl
    | inr layer =>
        refine ⟨crossIndex s, ?_⟩
        rw [holdProbeSource]
        rfl
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
  obtain ⟨e, he⟩ :=
    C.exists_eigenvalueEquiv
      (fun i => (energy i : ℂ))
      shift attachment p hqGood.1 hH
  have hdiagonal :
      localExtensionMatrix
          (fun i => (energy i : ℂ))
          p.1 attachment p.2 =
        C.unitaryEigenvectorMatrix hH e *
          Matrix.diagonal
            (fun i =>
              (C.realBranchEnergy
                (fun i => (energy i : ℂ))
                shift attachment p i : ℂ)) *
          star (C.unitaryEigenvectorMatrix hH e) :=
    C.localExtensionMatrix_eq_unitary_diagonal
      (fun i => (energy i : ℂ))
      shift attachment p hH e he
  have hnextMaximal :
      MaximallyProjectiveEnergy
        (C.realBranchEnergy
          (fun i => (energy i : ℂ))
          shift attachment p) :=
    C.realBranchEnergy_maximallyProjective
      (fun i => (energy i : ℂ))
      shift attachment p hqGood.1 hH hqMaximal
  have hnextFamily :
      HermitianObserverFamilyGood
        (unitaryLeafExtendedProbeMatrixFamily
          G anchor C oldProbe newProbe hH e) :=
    unitaryLeafExtendedProbeMatrixFamily_good
      G anchor C oldProbe newProbe
      holdProbeHermitian hnewProbeHermitian
      p hqGood.1 hH e he hqGood.2.1 hqGood.2.2
  exact ⟨attachment, ⟨attachmentCoefficient, rfl⟩,
    n, C, oldProbe, holdProbeOrigin, newProbe, q,
    hH, e, he, hdiagonal, hnextMaximal, hnextFamily⟩

end

end GaloisForLFunctions.HTGeometry
