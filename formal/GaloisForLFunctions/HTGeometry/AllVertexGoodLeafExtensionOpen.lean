import GaloisForLFunctions.HTGeometry.LocalExtensionChartProbeSupportOpenness

/-!
# A full open all-vertex-good leaf-extension neighborhood

The anchor-star witness is one point of the full physical local-extension
chart.  Continuity of every selected bra--ket amplitude upgrades that point
to a neighborhood on which all old observer graphs and the new-leaf graph
remain connected and nonbipartite simultaneously.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology
open scoped Matrix.Norms.Elementwise

/-- Real form of the anchor star used by the physical Hermitian slice. -/
def realAnchorStarLayerEdge
    {ρ : Type*} [DecidableEq ρ] (anchor : ρ) :
    Matrix ρ ρ ℝ :=
  fun r s =>
    if (r = anchor ∧ s ≠ anchor) ∨
        (s = anchor ∧ r ≠ anchor)
    then 1 else 0

/-- The real anchor star complexifies to the perturbative anchor star
exactly, including its real coupling strength. -/
theorem realLocalExtensionParameter_realAnchorStarLayerEdge
    {ρ : Type*} [DecidableEq ρ]
    (shift : ρ → ℝ) (anchor : ρ) (t : ℝ) :
    realLocalExtensionParameter
        (shift, t • realAnchorStarLayerEdge anchor) =
      ((fun r => (shift r : ℂ)),
        (t : ℂ) • anchorStarLayerEdge anchor) := by
  apply Prod.ext
  · rfl
  · ext r s
    change
      ((((t * realAnchorStarLayerEdge anchor r s) +
          (t * realAnchorStarLayerEdge anchor s r)) / 2 : ℝ) : ℂ) =
        (t : ℂ) * anchorStarLayerEdge anchor r s
    by_cases h :
        (r = anchor ∧ s ≠ anchor) ∨
          (s = anchor ∧ r ≠ anchor)
    · have hswap :
          (s = anchor ∧ r ≠ anchor) ∨
            (r = anchor ∧ s ≠ anchor) :=
        h.elim Or.inr Or.inl
      simp [realAnchorStarLayerEdge, anchorStarLayerEdge,
        h, hswap]
    · have hswap :
          ¬ ((s = anchor ∧ r ≠ anchor) ∨
            (r = anchor ∧ s ≠ anchor)) := by
        intro hs
        exact h (hs.elim Or.inr Or.inl)
      simp [realAnchorStarLayerEdge, anchorStarLayerEdge,
        h, hswap]

/-- Simultaneous goodness for arbitrary finite old- and new-probe index
families. -/
def AllVertexLocalExtensionChartGoodFamily
    {I ρ S : Type*} [Fintype I] [Fintype ρ]
    [DecidableEq I] [DecidableEq ρ]
    {ηOld : S → Type*} {ηNew : Type*}
    (energy : I → ℂ) (shift : ρ → ℂ)
    (attachment : Matrix I I ℂ)
    (C : LocalExtensionEigenbranchChart energy shift attachment)
    (oldProbe : ∀ s, ηOld s → Matrix I I ℂ)
    (newProbe : ηNew → Matrix ρ ρ ℂ)
    (p : (ρ → ℂ) × Matrix ρ ρ ℂ) : Prop :=
  (∀ s,
    (oldSystemLocalExtensionChartProbeSupportGraph
      energy shift attachment C (oldProbe s) p).Preconnected ∧
    ¬ (oldSystemLocalExtensionChartProbeSupportGraph
      energy shift attachment C (oldProbe s) p).IsBipartite) ∧
  (newLayerLocalExtensionChartProbeSupportGraph
    energy shift attachment C newProbe p).Preconnected ∧
  ¬ (newLayerLocalExtensionChartProbeSupportGraph
    energy shift attachment C newProbe p).IsBipartite

/-- **Open all-vertex-good leaf-extension theorem.** Every all-vertex-good
maximally projective input with a connected nonbipartite attachment channel
has a coded product center and one full local-extension chart containing a
nonempty open neighborhood on which all old observer graphs and the new
leaf graph are simultaneously connected and nonbipartite. -/
theorem
    exists_eventually_allVertexGood_leafExtension_open
    {I ρ S : Type*} [Fintype I] [Fintype ρ] [Fintype S]
    [DecidableEq I] [DecidableEq ρ] [DecidableEq S]
    [Nonempty I]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (anchor other : ρ) (hother : other ≠ anchor)
    (attachment : Matrix I I ℂ)
    (hattachmentSymm :
      ∀ x y, attachment x y = attachment y x)
    (hattachmentReal :
      ∀ x y,
        (starRingEnd ℂ) (attachment x y) = attachment x y)
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
      holdHermitian, hnewHermitian, hline⟩ :=
    exists_eventually_allVertexGood_leafExtensionChart
      energy hmax anchor other hother attachment
      hattachmentSymm hattachmentReal
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
    holdHermitian, hnewHermitian, htmem,
    ⟨hold₀, hnew₀⟩, ?_⟩
  filter_upwards [hU, hold, hnew] with p hpU hpold hpnew
  exact ⟨hpU, hpold, hpnew⟩

end

end GaloisForLFunctions.HTGeometry
