/-
# Extremality of the sorted gap-ratio map on the whole simple locus

The chart form of Kleinbock--Margulis extremality holds on every preconnected open piece of the
simple-spectrum locus.  In a second-countable space every open set is a countable union of balls,
and a ball is preconnected, so the exceptional set of the whole locus is a countable union of null
sets.

Main results:
* `volume_vwa_sortedGapRatio_eq_zero` — **the global extremality statement**.
-/
import GaloisForLFunctions.HTGeometry.SortedSpectrumGapExtremality

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D n : ℕ} {P : Fin N → Matrix (Fin D) (Fin D) ℂ}

/-- **Extremality of the sorted gap-ratio map on the whole simple locus.**  Every open subset of a
second-countable space is a countable union of balls, and each ball is a preconnected open piece of
the simple locus, so the chart statement globalises. -/
theorem volume_vwa_sortedGapRatio_eq_zero [NeZero N] (hn : 0 < n) (hP : ∀ a, (P a).IsHermitian)
    (hS : SpectrumEscapesRealRelations (Set.range (spectralEnsembleMatrix P)))
    {anchor clock : Fin D} {ι : Fin n → Fin D} (hι : Function.Injective ι)
    (hanchor : ∀ k, ι k ≠ anchor) (hclock : ∀ k, ι k ≠ clock) (hac : anchor ≠ clock) :
    volume {x ∈ simpleEnsembleLocus hP |
      KleinbockMargulis.VWA fun k =>
        anchoredGapRatioMap (sortedEnsembleSpectrum hP x) anchor clock ι k} = 0 := by
  classical
  set B : {p : (Fin N → ℝ) × ℝ // 0 < p.2 ∧ Metric.ball p.1 p.2 ⊆ simpleEnsembleLocus hP} →
      Set (Fin N → ℝ) := fun p => Metric.ball p.1.1 p.1.2 with hB
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable B
    (fun p => Metric.isOpen_ball)
  have hunion : (⋃ p, B p) = simpleEnsembleLocus hP := by
    refine Set.Subset.antisymm (Set.iUnion_subset fun p => p.2.2) ?_
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_simpleEnsembleLocus hP) x hx
    exact Set.mem_iUnion.mpr ⟨⟨(x, r), hr, hball⟩, Metric.mem_ball_self hr⟩
  have hsub : {x ∈ simpleEnsembleLocus hP |
        KleinbockMargulis.VWA fun k =>
          anchoredGapRatioMap (sortedEnsembleSpectrum hP x) anchor clock ι k}
      ⊆ ⋃ p ∈ T, {x ∈ B p |
        KleinbockMargulis.VWA fun k =>
          anchoredGapRatioMap (sortedEnsembleSpectrum hP x) anchor clock ι k} := by
    rintro x ⟨hxU, hxV⟩
    rw [← hunion, ← hT] at hxU
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hxU
    exact Set.mem_iUnion₂.mpr ⟨p, hp, hxp, hxV⟩
  refine measure_mono_null hsub ?_
  rw [measure_biUnion_null_iff hTc]
  intro p _
  exact theoremA_sortedGapRatio hn hP hS hι hanchor hclock hac Metric.isOpen_ball
    Metric.isPreconnected_ball ⟨p.1.1, Metric.mem_ball_self p.2.1⟩ p.2.2

end

end GaloisForLFunctions.HTGeometry
