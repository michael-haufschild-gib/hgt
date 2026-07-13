import GaloisForLFunctions.HTGeometry.NevanlinnaExpandedEvaluationCompactPatch
import GaloisForLFunctions.HTGeometry.CoefficientUniformJetEscape

/-!
# Compact-patch density for translated Nevanlinna jet packets

An expanded differential-evaluation row contains the jets at every translated node.  This module
performs the exact dependent reindexing
`(Σ x : row × shift, Fin (orders x.2)) ≃ row × (Σ i, Fin (orders i))` and instantiates the
uniform finite probe and stratified transversality theorem for that literal packet.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Topology
open scoped ENNReal OnePoint

noncomputable section

/-- Continuous real-linear reassociation of the combined translated-node jets into evaluation
rows. -/
def reshapeCombinedJetsCLM
    (row ι : Type*) [Fintype row] [Fintype ι] (orders : ι → ℕ) :
    ((Σ x : row × ι, Fin (orders x.2)) → ℂ) →L[ℝ]
      (row × (Σ i, Fin (orders i)) → ℂ) :=
  LinearMap.toContinuousLinearMap (reshapeCombinedJets row ι orders)

@[simp]
theorem reshapeCombinedJetsCLM_apply
    (row ι : Type*) [Fintype row] [Fintype ι] (orders : ι → ℕ)
    (x : (Σ p : row × ι, Fin (orders p.2)) → ℂ)
    (p : row × (Σ i, Fin (orders i))) :
    reshapeCombinedJetsCLM row ι orders x p =
      x ⟨(p.1, p.2.1), p.2.2⟩ :=
  rfl

/-- The continuous translated-jet reassociation is onto. -/
theorem reshapeCombinedJetsCLM_surjective
    (row ι : Type*) [Fintype row] [Fintype ι] (orders : ι → ℕ) :
    Function.Surjective (reshapeCombinedJetsCLM row ι orders) := by
  exact reshapeCombinedJets_surjective row ι orders

/-- **Translated Nevanlinna compact-patch density law.**  A compact regular family of all
row-by-translate nodes has a uniform finite-dimensional frozen-tangent probe.  The actual smooth
Nevanlinna row evaluation, after the exact dependent reassociation, densely avoids the literal
expanded coefficient-rank defect on the whole compact configuration patch. -/
theorem compact_translatedNevanlinnaExpandedEvaluation_has_dense_finiteProbe
    (projectiveGeometry : ClassicalComplexProjectiveIncidenceGeometry)
    (parametricAvoidance : ClassicalStratifiedParametricAvoidance)
    {H row κ ι ιf : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    [Fintype ιf] [DecidableEq ιf]
    (a q : ℂ → ℂ) (ha : ContDiff ℂ ⊤ a) (hq : ContDiff ℂ ⊤ q)
    (η : ℝ) (hη : 0 < η)
    (zf : ιf → ℂ) (hqf_inj : Function.Injective (fun i => q (zf i)))
    (hupperf : ∀ i, 0 < (q (zf i)).im)
    (nf : ιf → ℕ) (haf : ∀ i, a (zf i) ≠ 0)
    (hqdf : ∀ i, deriv q (zf i) ≠ 0)
    (degree : ℕ) (orders : ι → ℕ)
    (rowBase : row → ℂ) (hrowBase : Function.Injective rowBase)
    (exponent : κ → ((Σ i, Fin (orders i)) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree < Fintype.card row)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu] (hmu : mu.support.Infinite)
    (nodes : H → (row × ι → ℂ)) (hnodes : ContDiff ℝ ⊤ nodes)
    (U K : Set H) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hupper : ∀ h ∈ U, ∀ x, η ≤ (q (nodes h x)).im)
    (hqt_inj : ∀ h ∈ K, Function.Injective (fun x => q (nodes h x)))
    (hcross : ∀ h ∈ K, ∀ i x, q (zf i) ≠ q (nodes h x))
    (hat : ∀ h ∈ K, ∀ x, a (nodes h x) ≠ 0)
    (hqdt : ∀ h ∈ K, ∀ x, deriv q (nodes h x) ≠ 0)
    (hdim : Module.finrank ℝ H <
      2 * (Fintype.card row - Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    let frozen := projectiveNevanlinnaJetLinftyContinuousControl
      a q zf nf haf hqdf mu hupperf
    let S := LinearMap.ker frozen.toLinearMap
    ∃ V : Submodule ℝ S, V.FG ∧
      let control := fun h =>
        projectiveNevanlinnaJetExpansionSmoothControl
          a q (fun x : row × ι => orders x.2) mu (nodes h)
      let base := fun h =>
        reshapeCombinedJetsCLM row ι orders (control h (linftyOne mu))
      let direction := fun h =>
        (reshapeCombinedJetsCLM row ι orders).comp ((control h).domRestrict S)
      Dense (compactConfigurationAvoidance
        (smoothAffineControlFamily base direction)
        (expandedDifferentialEvaluationRankDefect
          degree (Fintype.card (Σ i, Fin (orders i))) rowBase exponent) K) := by
  dsimp only
  let frozen := projectiveNevanlinnaJetLinftyContinuousControl
    a q zf nf haf hqdf mu hupperf
  let S := LinearMap.ker frozen.toLinearMap
  letI : NormedSpace ℝ S := Submodule.normedSpace S
  let nodeLift : K → (row × ι → NevanlinnaUpperNodeAtLeast q η) :=
    fun h x => ⟨nodes h.1 x, hupper h.1 (hKU h.2) x⟩
  have hnodeLift : Continuous nodeLift := by
    apply continuous_pi
    intro x
    exact ((continuous_apply x).comp
      (hnodes.continuous.comp continuous_subtype_val)).subtype_mk _
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let Knode : Set (row × ι → NevanlinnaUpperNodeAtLeast q η) := Set.range nodeLift
  have hKnode : IsCompact Knode := isCompact_range hnodeLift
  obtain ⟨V, hVfg, hVsurj⟩ :=
    compact_regularNevanlinnaTargetFamily_has_uniform_finiteProbe
      a q ha hq η hη zf hqf_inj hupperf nf haf hqdf
      (fun x : row × ι => orders x.2) mu hmu Knode hKnode
      (fun z hz => by
        obtain ⟨h, rfl⟩ := hz
        exact hqt_inj h.1 h.2)
      (fun z hz i x => by
        obtain ⟨h, rfl⟩ := hz
        exact hcross h.1 h.2 i x)
      (fun z hz x => by
        obtain ⟨h, rfl⟩ := hz
        exact hat h.1 h.2 x)
      (fun z hz x => by
        obtain ⟨h, rfl⟩ := hz
        exact hqdt h.1 h.2 x)
  refine ⟨V, hVfg, ?_⟩
  dsimp only
  letI : NormedSpace ℝ V := Submodule.normedSpace V
  let control := fun h =>
    projectiveNevanlinnaJetExpansionSmoothControl
      a q (fun x : row × ι => orders x.2) mu (nodes h)
  let base := fun h =>
    reshapeCombinedJetsCLM row ι orders (control h (linftyOne mu))
  let direction := fun h =>
    (reshapeCombinedJetsCLM row ι orders).comp ((control h).domRestrict S)
  let directionV := fun h =>
    (reshapeCombinedJetsCLM row ι orders).comp
      (((control h).domRestrict S).domRestrict V)
  have hcontrol : ContDiffOn ℝ ⊤ control U := by
    exact (contDiffOn_projectiveNevanlinnaJetExpansionSmoothControl
      a q ha hq (fun x : row × ι => orders x.2) mu).comp hnodes.contDiffOn
        (fun h hh x => hη.trans_le (hupper h hh x))
  have hbase : ContDiffOn ℝ ⊤ base U := by
    exact (reshapeCombinedJetsCLM row ι orders).contDiff.comp_contDiffOn
      (hcontrol.clm_apply contDiffOn_const)
  have hdirection : ContDiffOn ℝ ⊤ direction U := by
    have hS : ContDiffOn ℝ ⊤ (fun h => (control h).domRestrict S) U := by
      have hsubS : ContDiffOn ℝ ⊤ (fun _ : H => S.subtypeL) U := contDiffOn_const
      simpa only [ContinuousLinearMap.domRestrict] using hcontrol.clm_comp hsubS
    have hreindex : ContDiffOn ℝ ⊤
        (fun _ : H => reshapeCombinedJetsCLM row ι orders) U := contDiffOn_const
    simpa only [direction] using hreindex.clm_comp hS
  have hdirectionV : ContDiffOn ℝ ⊤ directionV U := by
    have hS : ContDiffOn ℝ ⊤ (fun h => (control h).domRestrict S) U := by
      have hsubS : ContDiffOn ℝ ⊤ (fun _ : H => S.subtypeL) U := contDiffOn_const
      simpa only [ContinuousLinearMap.domRestrict] using hcontrol.clm_comp hsubS
    have hV : ContDiffOn ℝ ⊤
        (fun h => ((control h).domRestrict S).domRestrict V) U := by
      have hsubV : ContDiffOn ℝ ⊤ (fun _ : H => V.subtypeL) U := contDiffOn_const
      simpa only [ContinuousLinearMap.domRestrict] using hS.clm_comp hsubV
    have hreindex : ContDiffOn ℝ ⊤
        (fun _ : H => reshapeCombinedJetsCLM row ι orders) U := contDiffOn_const
    simpa only [directionV] using hreindex.clm_comp hV
  have hdirectionSurjK : ∀ h ∈ K, Function.Surjective (directionV h) := by
    intro h hh y
    obtain ⟨ys, hys⟩ := reshapeCombinedJetsCLM_surjective row ι orders y
    have hzmem : nodeLift ⟨h, hh⟩ ∈ Knode := Set.mem_range_self ⟨h, hh⟩
    obtain ⟨v, hv⟩ := hVsurj (nodeLift ⟨h, hh⟩) hzmem ys
    refine ⟨v, ?_⟩
    change reshapeCombinedJetsCLM row ι orders (control h v.1.1) = y
    have heq := projectiveNevanlinnaJetExpansionSmoothControl_eq_existing
      a q (fun x : row × ι => orders x.2) mu η hη (nodeLift ⟨h, hh⟩)
    rw [heq, hv, hys]
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
    projectiveGeometry parametricAvoidance degree
    (Fintype.card (Σ i, Fin (orders i))) rowBase hrowBase
    exponent hexponent hrows (fun h => base h + direction h center)
    directionV Usurj K hUsurj hK hKUsurj
  · exact (hbase.add (hdirection.clm_apply contDiffOn_const)).mono inter_subset_left
  · exact hdirectionV.mono inter_subset_left
  · exact fun h hh => hh.2
  · exact hdim

end

end GaloisForLFunctions.HTGeometry
