import GaloisForLFunctions.HTGeometry.SortedGapRatioGlobalExtremality
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.LinearFlowFourierPacketWindow

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D n : ℕ} {P : Fin N → Matrix (Fin D) (Fin D) ℂ}

/-- Strong (multiplicative) extremality of the sorted gap-ratio map on one
preconnected simple-spectrum chart. -/
theorem theoremA_sortedGapRatio_multiplicative [NeZero N]
    (hP : ∀ a, (P a).IsHermitian)
    (hS : SpectrumEscapesRealRelations (Set.range (spectralEnsembleMatrix P)))
    {anchor clock : Fin D} {ι : Fin n → Fin D} (hι : Function.Injective ι)
    (hanchor : ∀ k, ι k ≠ anchor) (hclock : ∀ k, ι k ≠ clock) (hac : anchor ≠ clock)
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUsimple : U ⊆ simpleEnsembleLocus hP) :
    volume {x ∈ U |
      KleinbockMargulis.VWMA fun k =>
        anchoredGapRatioMap (sortedEnsembleSpectrum hP x) anchor clock ι k} = 0 := by
  have hfamily : realAffineMatrix 0 P = spectralEnsembleMatrix P :=
    funext fun θ => realAffineMatrix_zero_eq_spectralEnsembleMatrix P θ
  refine KleinbockMargulis.theoremA_analytic_multiplicative hU hUc
    (analyticOnNhd_anchoredGapRatioMap hP hac ι hUsimple) ?_
  intro w hw
  refine no_constant_combination_gapRatio 0 P (by rw [hfamily]; exact hS)
    hι hanchor hclock hac hU hUne
    (fun q => sortedEnsembleSpectrum hP q)
    (fun q hq => injective_sortedEnsembleSpectrum hP (hUsimple hq)) ?_ w hw
  intro q _ i
  rw [realAffineMatrix_zero_eq_spectralEnsembleMatrix]
  exact matrixCharpolyRelation_sortedEnsembleSpectrum hP q i

/-- Strong extremality on the entire simple-spectrum locus. -/
theorem volume_vwma_sortedGapRatio_eq_zero [NeZero N]
    (hP : ∀ a, (P a).IsHermitian)
    (hS : SpectrumEscapesRealRelations (Set.range (spectralEnsembleMatrix P)))
    {anchor clock : Fin D} {ι : Fin n → Fin D} (hι : Function.Injective ι)
    (hanchor : ∀ k, ι k ≠ anchor) (hclock : ∀ k, ι k ≠ clock) (hac : anchor ≠ clock) :
    volume {x ∈ simpleEnsembleLocus hP |
      KleinbockMargulis.VWMA fun k =>
        anchoredGapRatioMap (sortedEnsembleSpectrum hP x) anchor clock ι k} = 0 := by
  classical
  set B : {p : (Fin N → ℝ) × ℝ //
      0 < p.2 ∧ Metric.ball p.1 p.2 ⊆ simpleEnsembleLocus hP} →
      Set (Fin N → ℝ) := fun p => Metric.ball p.1.1 p.1.2 with hB
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable B
    (fun p => Metric.isOpen_ball)
  have hunion : (⋃ p, B p) = simpleEnsembleLocus hP := by
    refine Set.Subset.antisymm (Set.iUnion_subset fun p => p.2.2) ?_
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
      (isOpen_simpleEnsembleLocus hP) x hx
    exact Set.mem_iUnion.mpr ⟨⟨(x, r), hr, hball⟩,
      Metric.mem_ball_self hr⟩
  have hsub : {x ∈ simpleEnsembleLocus hP |
        KleinbockMargulis.VWMA fun k =>
          anchoredGapRatioMap (sortedEnsembleSpectrum hP x) anchor clock ι k}
      ⊆ ⋃ p ∈ T, {x ∈ B p |
        KleinbockMargulis.VWMA fun k =>
          anchoredGapRatioMap (sortedEnsembleSpectrum hP x) anchor clock ι k} := by
    rintro x ⟨hxU, hxV⟩
    rw [← hunion, ← hT] at hxU
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hxU
    exact Set.mem_iUnion₂.mpr ⟨p, hp, hxp, hxV⟩
  refine measure_mono_null hsub ?_
  rw [measure_biUnion_null_iff hTc]
  intro p _
  exact theoremA_sortedGapRatio_multiplicative hP hS hι hanchor hclock hac
    Metric.isOpen_ball Metric.isPreconnected_ball
    ⟨p.1.1, Metric.mem_ball_self p.2.1⟩ p.2.2

end

end GaloisForLFunctions.HTGeometry
