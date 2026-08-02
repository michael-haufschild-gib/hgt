import GaloisForLFunctions.HTGeometry.HermitianAllVertexGoodLeafExtension
import GaloisForLFunctions.HTGeometry.AllVertexGoodLeafExtensionChart

/-!
# Arbitrary-Hermitian all-vertex extension in the common chart

The Hermitian perturbative witness is aligned with the same
multi-parameter eigenbranch chart used by spectral-rank genericity.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology

/-- **Arbitrary-Hermitian chart-aligned all-vertex extension.**  One coded
product center, one common local-extension chart, and finite Hermitian
probe families preserve every old observer and create the new observer
throughout one punctured anchor-star interval. -/
theorem
    exists_eventually_allVertexGood_leafExtensionChart_of_isHermitian
    {I ρ S : Type*} [Fintype I] [Fintype ρ] [Fintype S]
    [DecidableEq I] [DecidableEq ρ] [DecidableEq S]
    [Nonempty I]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (anchor other : ρ) (hother : other ≠ anchor)
    (attachment : Matrix I I ℂ)
    (hattachmentHermitian : attachment.IsHermitian)
    (hattachmentConnected :
      (transitionSupportGraph attachment).Preconnected)
    (hattachmentNonbipartite :
      ¬ (transitionSupportGraph attachment).IsBipartite)
    (G : S → SimpleGraph I)
    (hGconnected : ∀ s : S, (G s).Preconnected)
    (hGnonbipartite : ∀ s : S, ¬ (G s).IsBipartite)
    (baseProbe : ∀ s : S, GraphEdge (G s) → Matrix I I ℂ)
    (hbaseProbeHermitian :
      ∀ (s : S) (e : GraphEdge (G s)),
        (baseProbe s e).IsHermitian)
    (hbaseProbeEntry :
      ∀ (s : S) (e : GraphEdge (G s)),
        baseProbe s e e.1.1 e.1.2 ≠ 0)
    (crossSource crossMiddle crossTarget :
      ∀ _s : S, NonanchorLayer anchor → I)
    (crossProbe :
      ∀ _s : S, NonanchorLayer anchor → Matrix I I ℂ)
    (hcrossProbeHermitian :
      ∀ (s : S) (q : NonanchorLayer anchor),
        (crossProbe s q).IsHermitian)
    (hsourceMiddle :
      ∀ (s : S) (q : NonanchorLayer anchor),
        crossSource s q ≠ crossMiddle s q)
    (hmiddleTarget :
      ∀ (s : S) (q : NonanchorLayer anchor),
        crossMiddle s q ≠ crossTarget s q)
    (hattachment :
      ∀ (s : S) (q : NonanchorLayer anchor),
        attachment (crossSource s q) (crossMiddle s q) ≠ 0)
    (hcrossProbe :
      ∀ (s : S) (q : NonanchorLayer anchor),
        crossProbe s q (crossMiddle s q) (crossTarget s q) ≠ 0) :
    ∃ n : ℕ,
      let shift : ρ → ℂ :=
        fun r => (codedIntegerLayerShift anchor n r : ℂ)
      ∃ C : LocalExtensionEigenbranchChart
          (fun i => (energy i : ℂ)) shift attachment,
        ∃ oldProbe :
            ∀ s : S,
              Sum (GraphEdge (G s)) (NonanchorLayer anchor) →
                Matrix I I ℂ,
          ∃ newProbe :
              Sum (TransitionSupportEdge attachment × ρ)
                (NonanchorLayer anchor) → Matrix ρ ρ ℂ,
            (∀ s p, (oldProbe s p).IsHermitian) ∧
            (∀ s p,
              oldProbe s p =
                Sum.elim (baseProbe s) (crossProbe s) p) ∧
            (∀ p, (newProbe p).IsHermitian) ∧
            ∀ᶠ t : ℝ in 𝓝[≠] 0,
              (shift,
                  (t : ℂ) • anchorStarLayerEdge anchor) ∈ C.U ∧
              (∀ s,
                (oldSystemEigenbranchProbeSupportGraph
                    (layeredEnergy
                      (fun i => (energy i : ℂ)) shift)
                    (layerMatrixCoupling attachment
                      (anchorStarLayerEdge anchor))
                    (C.anchorStarBranch
                      (fun i => (energy i : ℂ))
                      shift attachment anchor)
                    (oldProbe s) t).Preconnected ∧
                  ¬ (oldSystemEigenbranchProbeSupportGraph
                    (layeredEnergy
                      (fun i => (energy i : ℂ)) shift)
                    (layerMatrixCoupling attachment
                      (anchorStarLayerEdge anchor))
                    (C.anchorStarBranch
                      (fun i => (energy i : ℂ))
                      shift attachment anchor)
                    (oldProbe s) t).IsBipartite) ∧
              (newLayerEigenbranchProbeSupportGraph
                  (layeredEnergy
                    (fun i => (energy i : ℂ)) shift)
                  (layerMatrixCoupling attachment
                    (anchorStarLayerEdge anchor))
                  (C.anchorStarBranch
                    (fun i => (energy i : ℂ))
                    shift attachment anchor)
                  newProbe t).Preconnected ∧
                ¬ (newLayerEigenbranchProbeSupportGraph
                  (layeredEnergy
                    (fun i => (energy i : ℂ)) shift)
                  (layerMatrixCoupling attachment
                    (anchorStarLayerEdge anchor))
                  (C.anchorStarBranch
                    (fun i => (energy i : ℂ))
                    shift attachment anchor)
                  newProbe t).IsBipartite := by
  obtain ⟨n, branch, oldProbe, newProbe,
      holdHermitian, holdProbeSource, hnewHermitian, hinj,
      hbranchAnalytic, hbranchBase, hbranchRoot, hgood⟩ :=
    exists_eventually_allVertexGood_leafExtension_of_isHermitian
      energy hmax anchor other hother attachment
      hattachmentHermitian
      hattachmentConnected hattachmentNonbipartite
      G hGconnected hGnonbipartite
      baseProbe hbaseProbeHermitian hbaseProbeEntry
      crossSource crossMiddle crossTarget crossProbe
      hcrossProbeHermitian hsourceMiddle hmiddleTarget
      hattachment hcrossProbe
  let shift : ρ → ℂ :=
    fun r => (codedIntegerLayerShift anchor n r : ℂ)
  let C : LocalExtensionEigenbranchChart
      (fun i => (energy i : ℂ)) shift attachment :=
    Classical.choice
      (exists_localExtensionEigenbranchChart
        (fun i => (energy i : ℂ)) shift attachment hinj)
  have heqComplex :
      ∀ᶠ t : ℂ in 𝓝 0, ∀ x,
        branch x t =
          C.anchorStarBranch
            (fun i => (energy i : ℂ))
            shift attachment anchor x t :=
    eventually_all_affineEigenbranches_eq_anchorStarBranch
      (fun i => (energy i : ℂ)) shift attachment C anchor
      hinj branch hbranchAnalytic hbranchBase hbranchRoot
  have hofReal :
      Tendsto (fun t : ℝ => (t : ℂ))
        (𝓝[≠] 0) (𝓝 0) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      inf_le_left
  have heqReal :
      ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ x,
        branch x t =
          C.anchorStarBranch
            (fun i => (energy i : ℂ))
            shift attachment anchor x t :=
    hofReal.eventually heqComplex
  have hchartReal :
      ∀ᶠ t : ℝ in 𝓝[≠] 0,
        (shift, (t : ℂ) • anchorStarLayerEdge anchor) ∈ C.U := by
    exact hofReal.eventually
      (C.eventually_anchorStar_mem
        (fun i => (energy i : ℂ))
        shift attachment anchor)
  refine ⟨n, C, oldProbe, newProbe,
    holdHermitian, holdProbeSource, hnewHermitian, ?_⟩
  filter_upwards [hgood, heqReal, hchartReal]
    with t hgoodT heqT hmemT
  have holdGraph :
      ∀ s,
        oldSystemEigenbranchProbeSupportGraph
            (layeredEnergy
              (fun i => (energy i : ℂ)) shift)
            (layerMatrixCoupling attachment
              (anchorStarLayerEdge anchor))
            branch (oldProbe s) t =
          oldSystemEigenbranchProbeSupportGraph
            (layeredEnergy
              (fun i => (energy i : ℂ)) shift)
            (layerMatrixCoupling attachment
              (anchorStarLayerEdge anchor))
            (C.anchorStarBranch
              (fun i => (energy i : ℂ))
              shift attachment anchor)
            (oldProbe s) t := by
    intro s
    exact oldSystemEigenbranchProbeSupportGraph_congr_branch_at
      _ _ _ _ _ _ heqT
  have hnewGraph :
      newLayerEigenbranchProbeSupportGraph
          (layeredEnergy
            (fun i => (energy i : ℂ)) shift)
          (layerMatrixCoupling attachment
            (anchorStarLayerEdge anchor))
          branch newProbe t =
        newLayerEigenbranchProbeSupportGraph
          (layeredEnergy
            (fun i => (energy i : ℂ)) shift)
          (layerMatrixCoupling attachment
            (anchorStarLayerEdge anchor))
          (C.anchorStarBranch
            (fun i => (energy i : ℂ))
            shift attachment anchor)
          newProbe t :=
    newLayerEigenbranchProbeSupportGraph_congr_branch_at
      _ _ _ _ _ _ heqT
  refine ⟨hmemT, ?_, ?_⟩
  · intro s
    rw [← holdGraph s]
    exact hgoodT.1 s
  · rw [← hnewGraph]
    exact hgoodT.2

end

end GaloisForLFunctions.HTGeometry
