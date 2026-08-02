import GaloisForLFunctions.HTGeometry.HermitianAllVertexGoodLeafExtensionChart
import GaloisForLFunctions.HTGeometry.AllVertexGoodLeafExtensionOpen

/-!
# Open arbitrary-Hermitian all-vertex leaf-extension neighborhood

The arbitrary-Hermitian anchor-star witness extends to a full open
neighborhood in the physical real local-extension slice.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology
open scoped Matrix.Norms.Elementwise

/-- **Open arbitrary-Hermitian all-vertex extension.**  Every
all-vertex-good maximally projective input with a connected,
nonbipartite Hermitian attachment has a coded product center and a
nonempty open chart neighborhood on which every old observer and the new
leaf remain simultaneously connected and nonbipartite. -/
theorem
    exists_eventually_allVertexGood_leafExtension_open_of_isHermitian
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
            ∃ p₀ : (ρ → ℂ) × Matrix ρ ρ ℂ,
              ∃ p₀R : (ρ → ℝ) × Matrix ρ ρ ℝ,
              realLocalExtensionParameter p₀R = p₀ ∧
              (∀ s q, (oldProbe s q).IsHermitian) ∧
              (∀ s q,
                oldProbe s q =
                  Sum.elim (baseProbe s) (crossProbe s) q) ∧
              (∀ q, (newProbe q).IsHermitian) ∧
              p₀ ∈ C.U ∧
              AllVertexLocalExtensionChartGoodFamily
                (fun i => (energy i : ℂ)) shift attachment C
                oldProbe newProbe p₀ ∧
              ∀ᶠ p in 𝓝 p₀,
                p ∈ C.U ∧
                AllVertexLocalExtensionChartGoodFamily
                  (fun i => (energy i : ℂ)) shift attachment C
                  oldProbe newProbe p := by
  obtain ⟨n, C, oldProbe, newProbe,
      holdHermitian, holdProbeSource, hnewHermitian, hline⟩ :=
    exists_eventually_allVertexGood_leafExtensionChart_of_isHermitian
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
  obtain ⟨t, htmem, htold, htnew⟩ := hline.exists
  let p₀ : (ρ → ℂ) × Matrix ρ ρ ℂ :=
    (shift, (t : ℂ) • anchorStarLayerEdge anchor)
  let p₀R : (ρ → ℝ) × Matrix ρ ρ ℝ :=
    (codedIntegerLayerShift anchor n,
      t • realAnchorStarLayerEdge anchor)
  have hp₀R :
      realLocalExtensionParameter p₀R = p₀ := by
    exact realLocalExtensionParameter_realAnchorStarLayerEdge
      (codedIntegerLayerShift anchor n) anchor t
  have hold₀ :
      ∀ s,
        (oldSystemLocalExtensionChartProbeSupportGraph
          (fun i => (energy i : ℂ)) shift attachment C
          (oldProbe s) p₀).Preconnected ∧
        ¬ (oldSystemLocalExtensionChartProbeSupportGraph
          (fun i => (energy i : ℂ)) shift attachment C
          (oldProbe s) p₀).IsBipartite := by
    intro s
    rw [oldSystemLocalExtensionChartProbeSupportGraph_anchorStar
      (fun i => (energy i : ℂ)) shift attachment C
      anchor (oldProbe s) t]
    exact htold s
  have hnew₀ :
      (newLayerLocalExtensionChartProbeSupportGraph
        (fun i => (energy i : ℂ)) shift attachment C
        newProbe p₀).Preconnected ∧
      ¬ (newLayerLocalExtensionChartProbeSupportGraph
        (fun i => (energy i : ℂ)) shift attachment C
        newProbe p₀).IsBipartite := by
    rw [newLayerLocalExtensionChartProbeSupportGraph_anchorStar
      (fun i => (energy i : ℂ)) shift attachment C
      anchor newProbe t]
    exact htnew
  have hold :
      ∀ᶠ p in 𝓝 p₀, ∀ s,
        (oldSystemLocalExtensionChartProbeSupportGraph
          (fun i => (energy i : ℂ)) shift attachment C
          (oldProbe s) p).Preconnected ∧
        ¬ (oldSystemLocalExtensionChartProbeSupportGraph
          (fun i => (energy i : ℂ)) shift attachment C
          (oldProbe s) p).IsBipartite := by
    exact Filter.eventually_all.mpr fun s =>
      eventually_oldSystemChartProbeSupportGraph_good
        (fun i => (energy i : ℂ)) shift attachment C
        (oldProbe s) p₀ htmem (hold₀ s).1 (hold₀ s).2
  have hnew :
      ∀ᶠ p in 𝓝 p₀,
        (newLayerLocalExtensionChartProbeSupportGraph
          (fun i => (energy i : ℂ)) shift attachment C
          newProbe p).Preconnected ∧
        ¬ (newLayerLocalExtensionChartProbeSupportGraph
          (fun i => (energy i : ℂ)) shift attachment C
          newProbe p).IsBipartite :=
    eventually_newLayerChartProbeSupportGraph_good
      (fun i => (energy i : ℂ)) shift attachment C
      newProbe p₀ htmem hnew₀.1 hnew₀.2
  have hU : C.U ∈ 𝓝 p₀ :=
    C.isOpen_U.mem_nhds htmem
  refine ⟨n, C, oldProbe, newProbe, p₀, p₀R, hp₀R,
    holdHermitian, holdProbeSource, hnewHermitian, htmem,
    ⟨hold₀, hnew₀⟩, ?_⟩
  filter_upwards [hU, hold, hnew] with p hpU hpold hpnew
  exact ⟨hpU, hpold, hpnew⟩

end

end GaloisForLFunctions.HTGeometry
