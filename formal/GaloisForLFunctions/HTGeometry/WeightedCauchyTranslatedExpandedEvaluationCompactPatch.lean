import GaloisForLFunctions.HTGeometry.NevanlinnaTranslatedExpandedEvaluationCompactPatch
import GaloisForLFunctions.HTGeometry.WeightedCauchyJetControlSmoothness
import GaloisForLFunctions.HTGeometry.WeightedJetControlSurjective

/-!
# Compact-patch density for translated weighted Cauchy jets

This is the arbitrary-base-measure counterpart of the projective Nevanlinna compact-patch theorem.
An integrable positive density supplies finite mass locally in the kernel, while the parameter space
remains the original `L∞(μ)`.  Infinite support gives exact control at every collision-free upper
node packet; compactness then extracts one finite-dimensional probe valid on the whole patch.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Topology
open scoped ENNReal OnePoint

noncomputable section

/-- **Weighted Cauchy compact-patch density law.**  A compact smooth family of distinct upper
row-by-translate nodes has a uniform finite-dimensional probe.  Its literal expanded differential
evaluation matrix densely avoids the full coefficient-rank defect on the whole compact patch. -/
theorem compact_weightedCauchyExpandedEvaluation_has_dense_finiteProbe
    {H row κ ι : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) (hμ : μ.support.Infinite)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hwpos : ∀ t, 0 < w t)
    (degree : ℕ) (orders : ι → ℕ)
    (rowBase : row → ℂ) (hrowBase : Function.Injective rowBase)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree < Fintype.card row)
    (background : H → (row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ))
    (nodes : H → (row × ι → ℂ)) (hnodes : ContDiff ℝ ⊤ nodes)
    (U K : Set H) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hbackground : ContDiffOn ℝ ⊤ background U)
    (hupper : ∀ h ∈ U, ∀ x, 0 < (nodes h x).im)
    (hnodes_inj : ∀ h ∈ K, Function.Injective (nodes h))
    (hdim : Module.finrank ℝ H <
      2 * (Fintype.card row - Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    ∃ V : Submodule ℝ (Lp ℝ (⊤ : ENNReal) μ), V.FG ∧
      let control := fun h =>
        weightedCauchyJetSmoothControl μ w hw
          (fun x : row × ι => orders x.2) (nodes h)
      let base := fun h => background h
      let direction := fun h =>
        (reshapeCombinedJetsFinCLM row ι orders).comp (control h)
      Dense (compactConfigurationAvoidance
        (smoothAffineControlFamily base direction)
        (expandedDifferentialEvaluationRankDefect
          degree (Fintype.card (Σ i, Fin (orders i))) rowBase exponent) K) := by
  let nodeLift : K → (row × ι → {z : ℂ // 0 < z.im}) :=
    fun h x => ⟨nodes h.1 x, hupper h.1 (hKU h.2) x⟩
  have hnodeLift : Continuous nodeLift := by
    apply continuous_pi
    intro x
    exact ((continuous_apply x).comp
      (hnodes.continuous.comp continuous_subtype_val)).subtype_mk _
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let Knode : Set (row × ι → {z : ℂ // 0 < z.im}) :=
    Set.range nodeLift
  have hKnode : IsCompact Knode := isCompact_range hnodeLift
  let target := fun z : row × ι → {z : ℂ // 0 < z.im} =>
    weightedCauchyJetSmoothControl μ w hw (fun x : row × ι => orders x.2)
      (fun x => (z x).1)
  have htargetOn : ContinuousOn target Knode := by
    have hval : Continuous
        (fun z : row × ι → {z : ℂ // 0 < z.im} =>
          fun x => (z x).1) := by
      apply continuous_pi
      intro x
      exact continuous_subtype_val.comp (continuous_apply x)
    exact (contDiffOn_weightedCauchyJetSmoothControl μ w hw
      (fun x : row × ι => orders x.2)).continuousOn.comp hval.continuousOn
        (fun z hz x => by simpa [nevanlinnaUpperPacketSet] using (z x).2)
  have htargetSurj : ∀ z ∈ Knode, Function.Surjective (target z) := by
    intro z hz
    have hzinj : Function.Injective (fun x => (z x).1) := by
      obtain ⟨h, rfl⟩ := hz
      exact hnodes_inj h.1 h.2
    change Function.Surjective
      (weightedCauchyJetSmoothControl μ w hw
        (fun x : row × ι => orders x.2) (fun x => (z x).1))
    rw [weightedCauchyJetSmoothControl_eq_weightedJetControl μ w hw _ _
      (fun x => (z x).2)]
    exact surjective_weightedJetControl μ hμ w hw hwpos (fun x => (z x).1)
      hzinj (fun x => by simpa using (z x).2) (fun x : row × ι => orders x.2)
  obtain ⟨V, hVfg, hVsurj⟩ :=
    compact_surjectiveControls_have_uniform_finiteProbe_of_continuousOn
      target Knode hKnode htargetOn htargetSurj
  refine ⟨V, hVfg, ?_⟩
  letI normedAddCommGroupV : NormedAddCommGroup V := Submodule.normedAddCommGroup V
  letI : NormedSpace ℝ V := Submodule.normedSpace V
  let control := fun h =>
    weightedCauchyJetSmoothControl μ w hw
      (fun x : row × ι => orders x.2) (nodes h)
  let base := fun h => background h
  let direction := fun h =>
    (reshapeCombinedJetsFinCLM row ι orders).comp (control h)
  let directionV := fun h =>
    (reshapeCombinedJetsFinCLM row ι orders).comp ((control h).domRestrict V)
  have hcontrol : ContDiffOn ℝ ⊤ control U := by
    exact (contDiffOn_weightedCauchyJetSmoothControl μ w hw
      (fun x : row × ι => orders x.2)).comp hnodes.contDiffOn
        (fun h hh x => by simpa [nevanlinnaUpperPacketSet] using hupper h hh x)
  have hbase : ContDiffOn ℝ ⊤ base U := hbackground
  have hdirection : ContDiffOn ℝ ⊤ direction U := by
    have hreindex : ContDiffOn ℝ ⊤
        (fun _ : H => reshapeCombinedJetsFinCLM row ι orders) U := contDiffOn_const
    simpa only [direction] using hreindex.clm_comp hcontrol
  have hdirectionV : ContDiffOn ℝ ⊤ directionV U := by
    have hV : ContDiffOn ℝ ⊤ (fun h => (control h).domRestrict V) U := by
      have hsubV : ContDiffOn ℝ ⊤ (fun _ : H => V.subtypeL) U := contDiffOn_const
      simpa only [ContinuousLinearMap.domRestrict] using hcontrol.clm_comp hsubV
    have hreindex : ContDiffOn ℝ ⊤
        (fun _ : H => reshapeCombinedJetsFinCLM row ι orders) U := contDiffOn_const
    simpa only [directionV] using hreindex.clm_comp hV
  have hdirectionSurjK : ∀ h ∈ K, Function.Surjective (directionV h) := by
    intro h hh y
    obtain ⟨ys, hys⟩ := reshapeCombinedJetsFinCLM_surjective row ι orders y
    have hzmem : nodeLift (⟨h, hh⟩ : K) ∈ Knode :=
      Set.mem_range_self (⟨h, hh⟩ : K)
    obtain ⟨v, hv⟩ := hVsurj (nodeLift (⟨h, hh⟩ : K)) hzmem ys
    refine ⟨v, ?_⟩
    change reshapeCombinedJetsFinCLM row ι orders (control h v.1) = y
    have hv' : control h v.1 = ys := by
      simpa only [target, nodeLift, control, ContinuousLinearMap.domRestrict_apply,
        Submodule.subtypeL_apply] using hv
    rw [hv', hys]
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
    degree (Fintype.card (Σ i, Fin (orders i))) rowBase hrowBase
    exponent hexponent hrows (fun h => base h + direction h center)
    directionV Usurj K hUsurj hKUsurj
  · exact (hbase.add (hdirection.clm_apply contDiffOn_const)).mono inter_subset_left
  · exact hdirectionV.mono inter_subset_left
  · exact fun h hh => hh.2
  · exact hdim

end

end GaloisForLFunctions.HTGeometry
