import GaloisForLFunctions.HTGeometry.AllVertexGoodLeafExtensionOpen
import GaloisForLFunctions.HTGeometry.ParityCompleteLocalExtensionRelationEscape

/-!
# Coupled all-observer transport and maximal-rank leaf extension

The open all-observer support law and the dense maximal-projective-rank law
are properties of the same real Hermitian local-extension slice.  Their
intersection therefore supplies one physical Hamiltonian realizing both
properties simultaneously.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Set Topology
open scoped Matrix.Norms.Elementwise

/-- The canonical coordinate decoder for the full real local-extension
slice is continuous. -/
theorem localExtensionSliceParameter_continuous
    {ρ : Type*} [Fintype ρ] :
    Continuous
      (localExtensionSliceParameter :
        (Fin (localExtensionSliceParameterCount ρ) → ℝ) →
          (ρ → ℝ) × Matrix ρ ρ ℝ) := by
  unfold localExtensionSliceParameter
  rw [continuous_prodMk]
  constructor
  · exact continuous_pi fun r =>
      continuous_apply
        (Fintype.equivFin (Sum ρ (ρ × ρ)) (Sum.inl r))
  · exact continuous_pi fun r =>
      continuous_pi fun s =>
        continuous_apply
          (Fintype.equivFin (Sum ρ (ρ × ρ))
            (Sum.inr (r, s)))

/-- The canonical coordinate decoder for the full real local-extension
slice is real analytic. -/
theorem localExtensionSliceParameter_analyticAt
    {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (p : Fin (localExtensionSliceParameterCount ρ) → ℝ) :
    AnalyticAt ℝ
      (localExtensionSliceParameter :
        (Fin (localExtensionSliceParameterCount ρ) → ℝ) →
          (ρ → ℝ) × Matrix ρ ρ ℝ) p := by
  unfold localExtensionSliceParameter
  apply AnalyticAt.prod
  · apply AnalyticAt.pi
    intro r
    exact (ContinuousLinearMap.proj (R := ℝ)
      (Fintype.equivFin (Sum ρ (ρ × ρ)) (Sum.inl r))).analyticAt p
  · apply AnalyticAt.pi
    intro r
    apply AnalyticAt.pi
    intro s
    exact (ContinuousLinearMap.proj (R := ℝ)
      (Fintype.equivFin (Sum ρ (ρ × ρ)) (Sum.inr (r, s)))).analyticAt p

/-- The canonical coordinate encoder for the full real local-extension
slice is continuous. -/
theorem localExtensionSliceCoordinates_continuous
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] :
    Continuous
      (localExtensionSliceCoordinates :
        ((ρ → ℝ) × Matrix ρ ρ ℝ) →
          (Fin (localExtensionSliceParameterCount ρ) → ℝ)) := by
  unfold localExtensionSliceCoordinates
  apply continuous_pi
  intro i
  cases h : (Fintype.equivFin (Sum ρ (ρ × ρ))).symm i with
  | inl r =>
      exact (continuous_apply r).comp continuous_fst
  | inr rs =>
      exact (continuous_apply rs.2).comp
        ((continuous_apply rs.1).comp continuous_snd)

/-- Complexification and symmetrization of a real local-extension parameter
is continuous for the product topologies used by the physical chart. -/
theorem realLocalExtensionParameter_continuous
    {ρ : Type*} [Fintype ρ] :
    Continuous
      (realLocalExtensionParameter :
        ((ρ → ℝ) × Matrix ρ ρ ℝ) →
          (ρ → ℂ) × Matrix ρ ρ ℂ) := by
  unfold realLocalExtensionParameter realSymmetricEdge
  fun_prop

/-- A complex-symmetric, entrywise real attachment matrix is Hermitian. -/
theorem isHermitian_of_symmetric_of_entrywise_real
    {I : Type*}
    (attachment : Matrix I I ℂ)
    (hsymmetric : ∀ x y, attachment x y = attachment y x)
    (hreal :
      ∀ x y,
        (starRingEnd ℂ) (attachment x y) = attachment x y) :
    attachment.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext x y
  rw [Matrix.conjTranspose_apply, hsymmetric]
  exact hreal x y

/-- **Coupled physical leaf-extension theorem.** Suppose a finite system has
maximal projective spectral rank and every indexed old observer has
connected, nonbipartite transition support.  If one connected,
nonbipartite Hermitian attachment channel reaches every required two-step
response, then for every finite attached factor of dimension at least two
there is one real Hermitian local extension such that:

* its complete product spectrum has maximal projective rank;
* every old observer retains connected, nonbipartite support; and
* the new factor acquires connected, nonbipartite support.

All three conclusions hold for the same Hamiltonian and the same labeled
simple-spectrum chart. -/
theorem
    exists_allVertexGood_maximallyProjective_leafExtension
    {I ρ S : Type*} [Fintype I] [Fintype ρ] [Fintype S]
    [DecidableEq I] [DecidableEq ρ] [DecidableEq S]
    [Nonempty I]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (anchor other : ρ) (hother : other ≠ anchor)
    (hcard : 2 ≤ Fintype.card ρ)
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
            ∃ q :
                Fin (localExtensionSliceParameterCount ρ) → ℝ,
              (∀ s p, (oldProbe s p).IsHermitian) ∧
              (∀ p, (newProbe p).IsHermitian) ∧
              MaximallyProjectiveEnergy
                (hermitianLocalExtensionSliceMatrix_isHermitian
                  (α := I) (ρ := ρ)
                  energy attachment
                  (isHermitian_of_symmetric_of_entrywise_real
                    attachment hattachmentSymm hattachmentReal)
                  q).eigenvalues ∧
              let p :=
                realLocalExtensionParameter
                  (localExtensionSliceParameter q)
              p ∈ C.U ∧
                AllVertexLocalExtensionChartGoodFamily
                  (fun i => (energy i : ℂ)) shift attachment C
                  oldProbe newProbe p := by
  let hattachmentHermitian : attachment.IsHermitian :=
    isHermitian_of_symmetric_of_entrywise_real
      attachment hattachmentSymm hattachmentReal
  rcases
      exists_eventually_allVertexGood_leafExtension_open
      energy hmax anchor other hother attachment
      hattachmentSymm hattachmentReal
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
  have hnewHermitian := hrest.2.2.1
  have hgood := hrest.2.2.2.2.2
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
  have hqMaximal :
      MaximallyProjectiveEnergy
        (hermitianLocalExtensionSliceMatrix_isHermitian
          energy attachment hattachmentHermitian q).eigenvalues := by
    exact hqMax
  refine ⟨n, C, oldProbe, newProbe, q,
    holdHermitian, hnewHermitian, ?_, ?_⟩
  · simpa only [hattachmentHermitian] using hqMaximal
  · exact hqGood

end

end GaloisForLFunctions.HTGeometry
