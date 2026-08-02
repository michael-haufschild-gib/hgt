import GaloisForLFunctions.HTGeometry.HermitianAllOldVerticesEndpointProbeSupportGraph
import GaloisForLFunctions.HTGeometry.HermitianEigenbranchProbeSupportGraph

/-!
# Arbitrary-Hermitian all-vertex-good leaf extension

One physical leaf extension simultaneously preserves every old observer and
creates a connected, nonbipartite observer at the new leaf, without a
real-symmetry restriction on the parent attachment.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology

/-- **Arbitrary-Hermitian all-vertex-good leaf extension.**  Let a
maximally projective real spectrum carry finitely many connected,
nonbipartite old-observer graphs.  Let one Hermitian attachment channel
have connected, nonbipartite transition support.  Attaching any finite
local factor with at least two labels produces one affine Hamiltonian
interval on which every old observer and the new leaf are simultaneously
connected and nonbipartite. -/
theorem
    exists_eventually_allVertexGood_leafExtension_of_isHermitian
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
    ∃ n : ℕ, ∃ branch : I × ρ → ℂ → ℂ,
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
          Function.Injective
            (layeredEnergy
              (fun i => (energy i : ℂ))
              (fun r =>
                (codedIntegerLayerShift anchor n r : ℂ))) ∧
          (∀ x, AnalyticAt ℂ (branch x) 0) ∧
          (∀ x,
            branch x 0 =
              layeredEnergy
                (fun i => (energy i : ℂ))
                (fun r =>
                  (codedIntegerLayerShift anchor n r : ℂ)) x) ∧
          (∀ x,
            ∀ᶠ t in 𝓝 0,
              matrixCharpolyRelation
                (Matrix.diagonal
                    (layeredEnergy
                      (fun i => (energy i : ℂ))
                      (fun r =>
                        (codedIntegerLayerShift anchor n r : ℂ))) +
                  t • layerMatrixCoupling attachment
                    (anchorStarLayerEdge anchor),
                  branch x t) = 0) ∧
          ∀ᶠ t : ℝ in 𝓝[≠] 0,
            (∀ s,
              (oldSystemEigenbranchProbeSupportGraph
                  (layeredEnergy
                    (fun i => (energy i : ℂ))
                    (fun r =>
                      (codedIntegerLayerShift anchor n r : ℂ)))
                  (layerMatrixCoupling attachment
                    (anchorStarLayerEdge anchor))
                  branch (oldProbe s) t).Preconnected ∧
                ¬ (oldSystemEigenbranchProbeSupportGraph
                  (layeredEnergy
                    (fun i => (energy i : ℂ))
                    (fun r =>
                      (codedIntegerLayerShift anchor n r : ℂ)))
                  (layerMatrixCoupling attachment
                    (anchorStarLayerEdge anchor))
                  branch (oldProbe s) t).IsBipartite) ∧
            (newLayerEigenbranchProbeSupportGraph
                (layeredEnergy
                  (fun i => (energy i : ℂ))
                  (fun r =>
                    (codedIntegerLayerShift anchor n r : ℂ)))
                (layerMatrixCoupling attachment
                  (anchorStarLayerEdge anchor))
                branch newProbe t).Preconnected ∧
              ¬ (newLayerEigenbranchProbeSupportGraph
                (layeredEnergy
                  (fun i => (energy i : ℂ))
                  (fun r =>
                    (codedIntegerLayerShift anchor n r : ℂ)))
                (layerMatrixCoupling attachment
                  (anchorStarLayerEdge anchor))
                branch newProbe t).IsBipartite := by
  obtain ⟨n, branch, oldProbe, holdProbeHermitian,
      holdProbeSource,
      hinj, hbranchAnalytic, hbranchBase, hbranchRoot, hold⟩ :=
    exists_eventually_allOldSystemProbeSupportGraphs_good_of_isHermitian
      energy hmax anchor attachment hattachmentHermitian
      G hGconnected hGnonbipartite
      baseProbe hbaseProbeHermitian hbaseProbeEntry
      crossSource crossMiddle crossTarget crossProbe
      hcrossProbeHermitian hsourceMiddle hmiddleTarget
      hattachment hcrossProbe
  let fullEnergy : I × ρ → ℂ :=
    layeredEnergy
      (fun i => (energy i : ℂ))
      (fun r => (codedIntegerLayerShift anchor n r : ℂ))
  have hfullEnergyReal :
      ∀ x, (starRingEnd ℂ) (fullEnergy x) = fullEnergy x := by
    rintro ⟨i, r⟩
    simp [fullEnergy, layeredEnergy, codedIntegerLayerShift]
  have hbranchReal :
      ∀ᶠ t : ℝ in 𝓝 0, ∀ x,
        (starRingEnd ℂ) (branch x t) = branch x t :=
    eventually_allLayerStarEigenbranches_real_of_isHermitian
      energy (codedIntegerLayerShift anchor n)
      anchor attachment hattachmentHermitian
      branch hbranchRoot
  obtain ⟨newProbe, hnewProbeHermitian, hnew⟩ :=
    exists_eventually_newLayerProbeSupportGraph_good_of_isHermitian
      fullEnergy hinj hfullEnergyReal
      attachment hattachmentHermitian anchor other hother
      branch hbranchAnalytic hbranchBase hbranchRoot hbranchReal
      hattachmentConnected hattachmentNonbipartite
  refine ⟨n, branch, oldProbe, newProbe,
    holdProbeHermitian, holdProbeSource, hnewProbeHermitian,
    hinj, hbranchAnalytic, hbranchBase, hbranchRoot, ?_⟩
  filter_upwards [hold, hnew] with t holdT hnewT
  exact ⟨holdT, hnewT⟩

end

end GaloisForLFunctions.HTGeometry
