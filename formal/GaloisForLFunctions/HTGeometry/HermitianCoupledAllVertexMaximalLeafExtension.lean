import GaloisForLFunctions.HTGeometry.HermitianAllVertexGoodLeafExtensionOpen
import GaloisForLFunctions.HTGeometry.CoupledAllVertexMaximalLeafExtension

/-!
# Composable Hermitian maximal-rank leaf extension

The open all-observer law and dense maximal-projective-rank law intersect
inside one real Hermitian extension slice even when the parent attachment
is an arbitrary Hermitian matrix.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Set Topology
open scoped Matrix.Norms.Elementwise

/-- **Composable coupled leaf-extension theorem.**  Suppose a finite
system has maximal projective spectral rank and every indexed old observer
has connected, nonbipartite transition support.  If one connected,
nonbipartite Hermitian attachment channel reaches every prescribed
two-step response, then every finite factor of dimension at least two
admits one Hermitian local extension whose complete spectrum is maximally
projective, whose old observers all remain good, and whose new factor is
good.  All conclusions hold for the same Hamiltonian and chart. -/
theorem
    exists_allVertexGood_maximallyProjective_leafExtension_of_isHermitian
    {I ρ S : Type*} [Fintype I] [Fintype ρ] [Fintype S]
    [DecidableEq I] [DecidableEq ρ] [DecidableEq S]
    [Nonempty I]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (anchor other : ρ) (hother : other ≠ anchor)
    (hcard : 2 ≤ Fintype.card ρ)
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
            ∃ q :
                Fin (localExtensionSliceParameterCount ρ) → ℝ,
              (∀ s p, (oldProbe s p).IsHermitian) ∧
              (∀ s p,
                oldProbe s p =
                  Sum.elim (baseProbe s) (crossProbe s) p) ∧
              (∀ p, (newProbe p).IsHermitian) ∧
              MaximallyProjectiveEnergy
                (hermitianLocalExtensionSliceMatrix_isHermitian
                  (α := I) (ρ := ρ)
                  energy attachment hattachmentHermitian q).eigenvalues ∧
              let p :=
                realLocalExtensionParameter
                  (localExtensionSliceParameter q)
              p ∈ C.U ∧
                AllVertexLocalExtensionChartGoodFamily
                  (fun i => (energy i : ℂ)) shift attachment C
                  oldProbe newProbe p := by
  rcases
      exists_eventually_allVertexGood_leafExtension_open_of_isHermitian
      energy hmax anchor other hother attachment
      hattachmentHermitian
      hattachmentConnected hattachmentNonbipartite
      G hGconnected hGnonbipartite
      baseProbe hbaseProbeHermitian hbaseProbeEntry
      crossSource crossMiddle crossTarget crossProbe
      hcrossProbeHermitian hsourceMiddle hmiddleTarget
      hattachment hcrossProbe
    with
      ⟨n, ⟨C, ⟨oldProbe, ⟨newProbe,
        ⟨p₀, ⟨p₀R, hrest⟩⟩⟩⟩⟩⟩
  have hp₀R := hrest.1
  have holdHermitian := hrest.2.1
  have holdProbeSource := hrest.2.2.1
  have hnewHermitian := hrest.2.2.2.1
  have hgood := hrest.2.2.2.2.2.2
  let shift : ρ → ℂ :=
    fun r => (codedIntegerLayerShift anchor n r : ℂ)
  have hsimple :
      Function.Injective
        (layeredEnergy
          (fun i => (energy i : ℂ)) shift) := by
    intro x y hxy
    apply C.simple (shift, 0) C.center_mem
    simpa only [shift, C.base] using hxy
  letI : Nonempty ρ := ⟨anchor⟩
  obtain ⟨_rankWitness, _hrankWitnessMax,
      hdense, _hresidual, _hnull⟩ :=
    hermitianLocalExtensionSliceMaximalSet_dense_residual_fullMeasure_of_goodSupport
      energy hmax (codedIntegerLayerShift anchor n)
      attachment hattachmentHermitian hsimple hcard
      hattachmentConnected hattachmentNonbipartite
  let q₀ : Fin (localExtensionSliceParameterCount ρ) → ℝ :=
    localExtensionSliceCoordinates p₀R
  let physicalParameter :
      (Fin (localExtensionSliceParameterCount ρ) → ℝ) →
        (ρ → ℂ) × Matrix ρ ρ ℂ :=
    realLocalExtensionParameter ∘ localExtensionSliceParameter
  have hq₀decode :
      localExtensionSliceParameter q₀ = p₀R := by
    exact localExtensionSliceParameter_coordinates p₀R
  have hq₀physical :
      physicalParameter q₀ = p₀ := by
    simp only [physicalParameter, Function.comp_apply, hq₀decode]
    exact hp₀R
  have hphysicalContinuousAt :
      ContinuousAt physicalParameter q₀ := by
    have hcomp :=
      (realLocalExtensionParameter_continuous (ρ := ρ)).comp
        (localExtensionSliceParameter_continuous (ρ := ρ))
    simpa only [physicalParameter] using hcomp.continuousAt
  have hpreimage :
      ∀ᶠ q in 𝓝 q₀,
        physicalParameter q ∈ C.U ∧
          AllVertexLocalExtensionChartGoodFamily
            (fun i => (energy i : ℂ)) shift attachment C
            oldProbe newProbe (physicalParameter q) := by
    have htend :
        Tendsto physicalParameter (𝓝 q₀) (𝓝 p₀) := by
      rw [← hq₀physical]
      exact hphysicalContinuousAt
    exact htend.eventually hgood
  obtain ⟨V, hVsub, hVopen, hq₀V⟩ :=
    mem_nhds_iff.mp hpreimage
  obtain ⟨q, hqMax, hqV⟩ :=
    hdense.exists_mem_open hVopen ⟨q₀, hq₀V⟩
  have hqGood := hVsub hqV
  refine ⟨n, C, oldProbe, newProbe, q,
    holdHermitian, holdProbeSource, hnewHermitian, hqMax, hqGood⟩

end

end GaloisForLFunctions.HTGeometry
