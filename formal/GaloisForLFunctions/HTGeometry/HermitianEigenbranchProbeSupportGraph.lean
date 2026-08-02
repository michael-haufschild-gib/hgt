import GaloisForLFunctions.HTGeometry.HermitianAllLayerEndpointPhysicalActivation
import GaloisForLFunctions.HTGeometry.EigenbranchProbeSupportGraph

/-!
# Arbitrary-Hermitian new-leaf support graphs

The new-factor support-graph inheritance law needs only a Hermitian old
attachment.  Entrywise reality and transpose symmetry are unnecessary.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology

/-- **Arbitrary-Hermitian new-leaf graph law.**  A connected,
nonbipartite transition-support graph is inherited by every finite new
local factor through one physical Hermitian anchor-star interaction and a
finite family of probes acting only on that factor.  The old attachment
may be any Hermitian matrix. -/
theorem
    exists_eventually_newLayerProbeSupportGraph_good_of_isHermitian
    {I ρ : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ] [Nonempty I]
    (energy : I × ρ → ℂ) (hinj : Function.Injective energy)
    (henergyReal :
      ∀ x, (starRingEnd ℂ) (energy x) = energy x)
    (transition : Matrix I I ℂ)
    (htransitionHermitian : transition.IsHermitian)
    (anchor other : ρ) (hother : other ≠ anchor)
    (branch : I × ρ → ℂ → ℂ)
    (hbranchAnalytic : ∀ x, AnalyticAt ℂ (branch x) 0)
    (hbranchBase : ∀ x, branch x 0 = energy x)
    (hbranchRoot :
      ∀ x,
        ∀ᶠ t in 𝓝 0,
          matrixCharpolyRelation
            (Matrix.diagonal energy +
              t • layerMatrixCoupling transition
                (anchorStarLayerEdge anchor),
              branch x t) = 0)
    (hbranchReal :
      ∀ᶠ t : ℝ in 𝓝 0, ∀ x,
        (starRingEnd ℂ) (branch x t) = branch x t)
    (hconnected :
      (transitionSupportGraph transition).Preconnected)
    (hnonbipartite :
      ¬ (transitionSupportGraph transition).IsBipartite) :
    ∃ probe :
        Sum (TransitionSupportEdge transition × ρ)
          (NonanchorLayer anchor) → Matrix ρ ρ ℂ,
      (∀ p, (probe p).IsHermitian) ∧
      ∀ᶠ t : ℝ in 𝓝[≠] 0,
        (newLayerEigenbranchProbeSupportGraph
            energy
            (layerMatrixCoupling transition
              (anchorStarLayerEdge anchor))
            branch probe t).Preconnected ∧
          ¬ (newLayerEigenbranchProbeSupportGraph
            energy
            (layerMatrixCoupling transition
              (anchorStarLayerEdge anchor))
            branch probe t).IsBipartite := by
  classical
  letI : Fintype (TransitionSupportEdge transition) :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  letI : Fintype (NonanchorLayer anchor) :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  let Edge := TransitionSupportEdge transition
  let Layer := NonanchorLayer anchor
  have hab : ∀ e : Edge, e.1.1 ≠ e.1.2 :=
    fun e => e.2.1
  have htransition :
      ∀ e : Edge, transition e.1.2 e.1.1 ≠ 0 := by
    intro e
    exact (mul_ne_zero_iff.mp e.2.2).2
  obtain ⟨sameProbe, hsameProbeHermitian, hsame⟩ :=
    exists_eventually_all_hermitianNewLayerSesquilinearProbes_ne_zero_of_isHermitian
      energy hinj henergyReal transition htransitionHermitian
      anchor other hother branch hbranchAnalytic hbranchBase
      hbranchRoot hbranchReal
      (fun e : Edge => e.1.1) (fun e : Edge => e.1.2)
      hab htransition
  let bridgeProbe : Layer → Matrix ρ ρ ℂ :=
    fun r => hermitianLayerCosineProbe r.1 anchor
  let bridgeProbeLift :
      Layer → Matrix (I × ρ) (I × ρ) ℂ :=
    fun r =>
      layerMatrixCoupling (1 : Matrix I I ℂ) (bridgeProbe r)
  let center : I := Classical.choice (inferInstance : Nonempty I)
  let bridgeSource : Layer → I × ρ :=
    fun r => (center, r.1)
  let bridgeTarget : Layer → I × ρ :=
    fun _ => (center, anchor)
  have hbridgeEntry :
      ∀ r : Layer,
        bridgeProbeLift r (bridgeSource r) (bridgeTarget r) ≠ 0 := by
    intro r
    simp [bridgeProbeLift, bridgeProbe, bridgeSource, bridgeTarget,
      layerMatrixCoupling, hermitianLayerCosineProbe,
      directedLayerMatrix, r.2]
  have hbridgeRow :
      ∀ᶠ t : ℝ in 𝓝 0, ∀ r : Layer,
        affineEigenbranchRowColumnMatrixProbe
          energy
          (layerMatrixCoupling transition
            (anchorStarLayerEdge anchor))
          (branch (bridgeSource r)) (branch (bridgeTarget r))
          (bridgeProbeLift r)
          (bridgeSource r) (bridgeTarget r) t ≠ 0 :=
    eventually_all_affineRowColumnMatrixProbes_ne_zero_of_base_entries
      energy hinj
      (layerMatrixCoupling transition
        (anchorStarLayerEdge anchor))
      branch hbranchAnalytic hbranchBase
      bridgeProbeLift bridgeSource bridgeTarget hbridgeEntry
  have hbridgePhysical :
      ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ r : Layer,
        affineEigenbranchSesquilinearMatrixProbe
          energy
          (layerMatrixCoupling transition
            (anchorStarLayerEdge anchor))
          (branch (bridgeSource r)) (branch (bridgeTarget r))
          (bridgeProbeLift r)
          (bridgeSource r) (bridgeTarget r) t ≠ 0 := by
    have hbridgeRowPunctured :
        ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ r : Layer,
          affineEigenbranchRowColumnMatrixProbe
            energy
            (layerMatrixCoupling transition
              (anchorStarLayerEdge anchor))
            (branch (bridgeSource r)) (branch (bridgeTarget r))
            (bridgeProbeLift r)
            (bridgeSource r) (bridgeTarget r) t ≠ 0 :=
      Filter.Eventually.filter_mono inf_le_left hbridgeRow
    have hbranchRealPunctured :
        ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ x,
          (starRingEnd ℂ) (branch x t) = branch x t :=
      Filter.Eventually.filter_mono inf_le_left hbranchReal
    filter_upwards
      [hbridgeRowPunctured, hbranchRealPunctured]
        with t ht hreal
    intro r
    rw [
      affineEigenbranchSesquilinearMatrixProbe_eq_rowColumn_of_isHermitian
        energy
        (layerMatrixCoupling transition
          (anchorStarLayerEdge anchor))
        (branch (bridgeSource r)) (branch (bridgeTarget r))
        (bridgeProbeLift r)
        (bridgeSource r) (bridgeTarget r) t]
    · exact ht r
    · apply affineBranchCharacteristicMatrix_isHermitian
      · apply affineMatrix_isHermitian_real_of_isHermitian
        · exact henergyReal
        · exact
            layerMatrixCoupling_isHermitian
              htransitionHermitian
              (anchorStarLayerEdge_isHermitian anchor)
      · exact hreal (bridgeSource r)
  let probe :
      Sum (Edge × ρ) Layer → Matrix ρ ρ ℂ
    | Sum.inl er => sameProbe er.1 er.2
    | Sum.inr r => bridgeProbe r
  refine ⟨probe, ?_, ?_⟩
  · intro p
    cases p with
    | inl er => exact hsameProbeHermitian er.1 er.2
    | inr r =>
        exact hermitianLayerCosineProbe_isHermitian r.1 anchor
  · filter_upwards [hsame, hbridgePhysical] with t hsameT hbridgeT
    have hle :
        anchoredReplicaGraph
            (transitionSupportGraph transition)
            anchor (fun _ => center) (fun _ => center) ≤
          newLayerEigenbranchProbeSupportGraph
            energy
            (layerMatrixCoupling transition
              (anchorStarLayerEdge anchor))
            branch probe t := by
      apply anchoredReplicaGraph_le_newLayerProbeSupportGraph
      · intro a b habEdge r
        let e : Edge := ⟨(a, b), habEdge⟩
        refine ⟨Sum.inl (e, r), ?_⟩
        simpa [probe, e] using hsameT e r
      · intro r hr
        let q : Layer := ⟨r, hr⟩
        refine ⟨Sum.inr q, ?_⟩
        simpa [probe, bridgeProbeLift, bridgeSource,
          bridgeTarget, q] using hbridgeT q
    exact ⟨
      newLayerProbeSupportGraph_preconnected
        (transitionSupportGraph transition) hconnected
        anchor (fun _ => center) (fun _ => center)
        energy
        (layerMatrixCoupling transition
          (anchorStarLayerEdge anchor))
        branch probe t hle,
      newLayerProbeSupportGraph_not_isBipartite
        (transitionSupportGraph transition) hnonbipartite
        anchor (fun _ => center) (fun _ => center)
        energy
        (layerMatrixCoupling transition
          (anchorStarLayerEdge anchor))
        branch probe t hle⟩

end

end GaloisForLFunctions.HTGeometry
