import GaloisForLFunctions.HTGeometry.ProjectiveNevanlinnaRowEvaluationSmoothness
import GaloisForLFunctions.HTGeometry.CompactNevanlinnaUniformProbe
import GaloisForLFunctions.HTGeometry.ExpandedEvaluationCompactPatchDensity

/-!
# Compact-patch expanded-evaluation density for the actual Nevanlinna family

This module instantiates the formal compact uniform probe in the smooth row-evaluation family and
feeds it to the projective-incidence/Whitney/Hirsch density theorem.  It is the project-specific
compact-patch density statement that was missing from the paper.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Topology
open scoped ENNReal OnePoint

noncomputable section

/-- Reindex a constant-order sigma jet packet by the literal row-block product used in the
expanded evaluation matrix. -/
def constantJetSigmaToProductCLM
    {row : Type} [Fintype row] (n : ℕ) :
    ((Σ _ : row, Fin n) → ℂ) →L[ℝ] (row × Fin n → ℂ) :=
  ({ toFun := fun x p => x ⟨p.1, p.2⟩
     map_add' := by intro x y; rfl
     map_smul' := by intro c x; rfl } :
      ((Σ _ : row, Fin n) → ℂ) →ₗ[ℝ] (row × Fin n → ℂ)).mkContinuous 1
    (fun x => by
      rw [one_mul]
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2
      intro p
      exact norm_le_pi_norm x ⟨p.1, p.2⟩)

@[simp]
theorem constantJetSigmaToProductCLM_apply
    {row : Type} [Fintype row] (n : ℕ)
    (x : (Σ _ : row, Fin n) → ℂ) (p : row × Fin n) :
    constantJetSigmaToProductCLM n x p = x ⟨p.1, p.2⟩ :=
  rfl

/-- The constant-order sigma/product reindexing is onto. -/
theorem constantJetSigmaToProductCLM_surjective
    {row : Type} [Fintype row] (n : ℕ) :
    Function.Surjective (constantJetSigmaToProductCLM (row := row) n) := by
  intro y
  refine ⟨fun s => y (s.1, s.2), ?_⟩
  funext p
  rfl

/-- On an open set where a continuous-linear-map family is continuous, its surjective members
form an open subset.  Finite-dimensionality is needed only in the target, through the determinant
of a chosen right inverse. -/
theorem isOpen_inter_surjective_continuousLinearMap_family
    {H X Y : Type}
    [TopologicalSpace H]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (L : H → (X →L[ℝ] Y)) (U : Set H)
    (hU : IsOpen U) (hL : ContinuousOn L U) :
    IsOpen (U ∩ {h | Function.Surjective (L h)}) := by
  rw [isOpen_iff_mem_nhds]
  intro h hh
  have hLat : ContinuousAt L h := (hL h hh.1).continuousAt (hU.mem_nhds hh.1)
  have hrange : (L h).toLinearMap.range = ⊤ := LinearMap.range_eq_top.mpr hh.2
  obtain ⟨s, hs⟩ := (L h).toLinearMap.exists_rightInverse_of_surjective hrange
  let sc : Y →L[ℝ] X := LinearMap.toContinuousLinearMap s
  let g : H → (Y →L[ℝ] Y) := fun h' => (L h').comp sc
  have hg : ContinuousAt g h := hLat.clm_comp continuousAt_const
  have hgh : g h = ContinuousLinearMap.id ℝ Y := by
    apply ContinuousLinearMap.ext
    intro y
    exact LinearMap.congr_fun hs y
  have hdet : (g h).det ≠ 0 := by
    rw [hgh]
    simp [ContinuousLinearMap.det, LinearMap.det_id]
  have hevent : ∀ᶠ h' in 𝓝 h, (g h').det ≠ 0 :=
    (ContinuousLinearMap.continuous_det.continuousAt.comp hg).eventually_ne hdet
  have hsurjN : {h' | Function.Surjective (L h')} ∈ 𝓝 h := by
    filter_upwards [hevent] with h' hdet'
    intro y
    let e : Y ≃L[ℝ] Y := (g h').toContinuousLinearEquivOfDetNeZero hdet'
    refine ⟨sc (e.symm y), ?_⟩
    change g h' (e.symm y) = y
    exact e.apply_symm_apply y
  exact Filter.inter_mem (hU.mem_nhds hh.1) hsurjN

/-- **Actual Nevanlinna compact-patch density law.**  One compact regular target-node family,
the formal uniform finite probe, the smooth row-evaluation theorem, and the projective incidence
codimension law produce a finite-dimensional probe whose parameters densely avoid the literal
expanded rank defect over the whole compact configuration patch. -/
theorem compact_nevanlinnaExpandedEvaluation_has_dense_finiteProbe
    (projectiveGeometry : ClassicalComplexProjectiveIncidenceGeometry)
    (parametricAvoidance : ClassicalStratifiedParametricAvoidance)
    {H row κ ιf : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ιf] [DecidableEq ιf]
    (a q : ℂ → ℂ) (ha : ContDiff ℂ ⊤ a) (hq : ContDiff ℂ ⊤ q)
    (η : ℝ) (hη : 0 < η)
    (zf : ιf → ℂ) (hqf_inj : Function.Injective (fun i => q (zf i)))
    (hupperf : ∀ i, 0 < (q (zf i)).im)
    (nf : ιf → ℕ) (haf : ∀ i, a (zf i) ≠ 0)
    (hqdf : ∀ i, deriv q (zf i) ≠ 0)
    (degree jetOrder : ℕ)
    (rowBase : row → ℂ) (hrowBase : Function.Injective rowBase)
    (exponent : κ → (Fin jetOrder →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree < Fintype.card row)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu] (hmu : mu.support.Infinite)
    (nodes : H → (row → ℂ)) (hnodes : ContDiff ℝ ⊤ nodes)
    (U K : Set H) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hupper : ∀ h ∈ U, ∀ i, η ≤ (q (nodes h i)).im)
    (hqt_inj : ∀ h ∈ K, Function.Injective (fun i => q (nodes h i)))
    (hcross : ∀ h ∈ K, ∀ i j, q (zf i) ≠ q (nodes h j))
    (hat : ∀ h ∈ K, ∀ i, a (nodes h i) ≠ 0)
    (hqdt : ∀ h ∈ K, ∀ i, deriv q (nodes h i) ≠ 0)
    (hdim : Module.finrank ℝ H <
      2 * (Fintype.card row - Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    let frozen := projectiveNevanlinnaJetLinftyContinuousControl
      a q zf nf haf hqdf mu hupperf
    let S := LinearMap.ker frozen.toLinearMap
    ∃ V : Submodule ℝ S, V.FG ∧
      let control := fun h =>
        projectiveNevanlinnaJetExpansionSmoothControl
          a q (fun _ : row => jetOrder) mu (nodes h)
      let base := fun h =>
        constantJetSigmaToProductCLM jetOrder (control h (linftyOne mu))
      let direction := fun h =>
        (constantJetSigmaToProductCLM jetOrder).comp
          ((control h).domRestrict S)
      Dense (compactConfigurationAvoidance
        (smoothAffineControlFamily base direction)
        (expandedDifferentialEvaluationRankDefect
          degree jetOrder rowBase exponent) K) := by
  dsimp only
  let frozen := projectiveNevanlinnaJetLinftyContinuousControl
    a q zf nf haf hqdf mu hupperf
  let S := LinearMap.ker frozen.toLinearMap
  haveI normedSpaceS : NormedSpace ℝ S := Submodule.normedSpace S
  let nodeLift : K → (row → NevanlinnaUpperNodeAtLeast q η) :=
    fun h i => ⟨nodes h.1 i, hupper h.1 (hKU h.2) i⟩
  have hnodeLift : Continuous nodeLift := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp (hnodes.continuous.comp continuous_subtype_val)).subtype_mk _
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let Knode : Set (row → NevanlinnaUpperNodeAtLeast q η) := Set.range nodeLift
  have hKnode : IsCompact Knode := isCompact_range hnodeLift
  obtain ⟨V, hVfg, hVsurj⟩ :=
    compact_regularNevanlinnaTargetFamily_has_uniform_finiteProbe
      a q ha hq η hη zf hqf_inj hupperf nf haf hqdf
      (fun _ : row => jetOrder) mu hmu Knode hKnode
      (fun z hz => by
        obtain ⟨h, rfl⟩ := hz
        exact hqt_inj h.1 h.2)
      (fun z hz i j => by
        obtain ⟨h, rfl⟩ := hz
        exact hcross h.1 h.2 i j)
      (fun z hz i => by
        obtain ⟨h, rfl⟩ := hz
        exact hat h.1 h.2 i)
      (fun z hz i => by
        obtain ⟨h, rfl⟩ := hz
        exact hqdt h.1 h.2 i)
  refine ⟨V, hVfg, ?_⟩
  dsimp only
  haveI normedSpaceV : NormedSpace ℝ V := Submodule.normedSpace V
  let control := fun h =>
    projectiveNevanlinnaJetExpansionSmoothControl
      a q (fun _ : row => jetOrder) mu (nodes h)
  let base := fun h =>
    constantJetSigmaToProductCLM jetOrder (control h (linftyOne mu))
  let direction := fun h =>
    (constantJetSigmaToProductCLM jetOrder).comp
      ((control h).domRestrict S)
  let directionV := fun h =>
    (constantJetSigmaToProductCLM jetOrder).comp
      (((control h).domRestrict S).domRestrict V)
  have hcontrol : ContDiffOn ℝ ⊤ control U := by
    exact (contDiffOn_projectiveNevanlinnaJetExpansionSmoothControl
      a q ha hq (fun _ : row => jetOrder) mu).comp hnodes.contDiffOn
        (fun h hh i => hη.trans_le (hupper h hh i))
  have hbase : ContDiffOn ℝ ⊤ base U := by
    exact (constantJetSigmaToProductCLM jetOrder).contDiff.comp_contDiffOn
      (hcontrol.clm_apply contDiffOn_const)
  have hdirection : ContDiffOn ℝ ⊤ direction U := by
    have hS : ContDiffOn ℝ ⊤
        (fun h => (control h).domRestrict S) U := by
      have hsubS : ContDiffOn ℝ ⊤
          (fun _ : H => S.subtypeL) U := contDiffOn_const
      simpa only [ContinuousLinearMap.domRestrict] using
        hcontrol.clm_comp hsubS
    have hreindex : ContDiffOn ℝ ⊤
        (fun _ : H => constantJetSigmaToProductCLM
          (row := row) jetOrder) U := contDiffOn_const
    simpa only [direction] using
      hreindex.clm_comp hS
  have hdirectionV : ContDiffOn ℝ ⊤ directionV U := by
    have hS : ContDiffOn ℝ ⊤
        (fun h => (control h).domRestrict S) U := by
      have hsubS : ContDiffOn ℝ ⊤
          (fun _ : H => S.subtypeL) U := contDiffOn_const
      simpa only [ContinuousLinearMap.domRestrict] using
        hcontrol.clm_comp hsubS
    have hV : ContDiffOn ℝ ⊤
        (fun h => ((control h).domRestrict S).domRestrict V) U := by
      have hsubV : ContDiffOn ℝ ⊤
          (fun _ : H => V.subtypeL) U := contDiffOn_const
      simpa only [ContinuousLinearMap.domRestrict] using
        hS.clm_comp hsubV
    have hreindex : ContDiffOn ℝ ⊤
        (fun _ : H => constantJetSigmaToProductCLM
          (row := row) jetOrder) U := contDiffOn_const
    simpa only [directionV] using
      hreindex.clm_comp hV
  have hdirectionSurjK : ∀ h ∈ K, Function.Surjective (directionV h) := by
    intro h hh y
    obtain ⟨ys, hys⟩ := constantJetSigmaToProductCLM_surjective jetOrder y
    have hzmem : nodeLift ⟨h, hh⟩ ∈ Knode := Set.mem_range_self ⟨h, hh⟩
    obtain ⟨v, hv⟩ := hVsurj (nodeLift ⟨h, hh⟩) hzmem ys
    refine ⟨v, ?_⟩
    change constantJetSigmaToProductCLM jetOrder
      (control h v.1.1) = y
    have heq := projectiveNevanlinnaJetExpansionSmoothControl_eq_existing
      a q (fun _ : row => jetOrder) mu η hη (nodeLift ⟨h, hh⟩)
    rw [heq]
    rw [hv, hys]
  let Usurj : Set H := U ∩ {h | Function.Surjective (directionV h)}
  have hUsurj : IsOpen Usurj :=
    isOpen_inter_surjective_continuousLinearMap_family
      directionV U hU hdirectionV.continuousOn
  have hKUsurj : K ⊆ Usurj := fun h hh => ⟨hKU hh, hdirectionSurjK h hh⟩
  apply dense_compactConfigurationAvoidance_of_dense_submodule_perturbations
    V base direction
  intro center
  letI : Module.Finite ℝ V := Module.Finite.of_fg hVfg
  apply expandedEvaluation_affineProbe_compactPatchAvoidance_dense
    projectiveGeometry parametricAvoidance degree jetOrder rowBase hrowBase
    exponent hexponent hrows (fun h => base h + direction h center)
    directionV Usurj K hUsurj hK hKUsurj
  · exact (hbase.add (hdirection.clm_apply contDiffOn_const)).mono inter_subset_left
  · exact hdirectionV.mono inter_subset_left
  · exact fun h hh => hh.2
  · exact hdim

end

end GaloisForLFunctions.HTGeometry
