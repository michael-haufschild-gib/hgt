import GaloisForLFunctions.HTGeometry.SpectralGapRatioExtremality
import GaloisForLFunctions.HTGeometry.SimpleSpectrumOpen

/-!
# Extremality of the sorted gap and gap-ratio maps of a Hermitian coefficient family

The canonical increasing labelling of the spectrum of `∑_a θ_a P_a` is real-analytic on the
simple-spectrum locus, which is open.  So on any preconnected open piece of that locus the anchored
gap map and the anchored gap-ratio map are analytic, and the escape property of the family makes
them nondegenerate — whence Kleinbock--Margulis extremality.

## Main results

* `simpleEnsembleLocus`, `isOpen_simpleEnsembleLocus` — the chart.
* `analyticOnNhd_anchoredGapMap`, `analyticOnNhd_anchoredGapRatioMap`.
* `theoremA_sortedGap`, `theoremA_sortedGapRatio` — almost every parameter of the chart is not
  simultaneously very well approximable in the sorted gaps, respectively the sorted gap ratios.
-/

open MeasureTheory Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D n : ℕ} {P : Fin N → Matrix (Fin D) (Fin D) ℂ}

theorem realAffineMatrix_zero_eq_spectralEnsembleMatrix
    (P : Fin N → Matrix (Fin D) (Fin D) ℂ) (θ : Fin N → ℝ) :
    realAffineMatrix 0 P θ = spectralEnsembleMatrix P θ := by
  ext i j
  simp [realAffineMatrix, spectralEnsembleMatrix, Matrix.sum_apply, Matrix.smul_apply]

/-- Each value of the sorted spectrum is a root of the characteristic relation. -/
theorem matrixCharpolyRelation_sortedEnsembleSpectrum
    (hP : ∀ a, (P a).IsHermitian) (θ : Fin N → ℝ) (j : Fin D) :
    matrixCharpolyRelation
      (spectralEnsembleMatrix P θ, ((sortedEnsembleSpectrum hP θ j : ℝ) : ℂ)) = 0 :=
  hermitianEigenvalue_matrixCharpolyRelation _ (isHermitian_spectralEnsembleMatrix hP θ) _

/-- The parameters at which the family has a simple spectrum. -/
def simpleEnsembleLocus (hP : ∀ a, (P a).IsHermitian) : Set (Fin N → ℝ) :=
  {θ | Function.Injective (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues}

theorem isOpen_simpleEnsembleLocus (hP : ∀ a, (P a).IsHermitian) :
    IsOpen (simpleEnsembleLocus hP) :=
  isOpen_simpleSpectrumLocus (continuous_spectralEnsembleMatrix P)
    (fun θ => isHermitian_spectralEnsembleMatrix hP θ)

theorem injective_sortedEnsembleSpectrum (hP : ∀ a, (P a).IsHermitian)
    {θ : Fin N → ℝ} (hθ : θ ∈ simpleEnsembleLocus hP) :
    Function.Injective (sortedEnsembleSpectrum hP θ) :=
  injective_sortedTuple hθ

theorem analyticOnNhd_anchoredGapMap (hP : ∀ a, (P a).IsHermitian)
    {scale : ℝ} (hscale : scale ≠ 0) (anchor : Fin D) (ι : Fin n → Fin D)
    {U : Set (Fin N → ℝ)} (hU : U ⊆ simpleEnsembleLocus hP) :
    AnalyticOnNhd ℝ
      (fun q => anchoredGapMap scale (sortedEnsembleSpectrum hP q) anchor ι) U := by
  intro θ hθ
  refine analyticAt_pi_iff.mpr fun k => ?_
  have hnum :
      AnalyticAt ℝ
        (fun q : Fin N → ℝ =>
          sortedEnsembleSpectrum hP q (ι k) - sortedEnsembleSpectrum hP q anchor) θ :=
    (analyticAt_sortedEnsembleSpectrum hP (hU hθ) (ι k)).sub
      (analyticAt_sortedEnsembleSpectrum hP (hU hθ) anchor)
  exact hnum.div analyticAt_const hscale

theorem analyticOnNhd_anchoredGapRatioMap (hP : ∀ a, (P a).IsHermitian)
    {anchor clock : Fin D} (hac : anchor ≠ clock) (ι : Fin n → Fin D)
    {U : Set (Fin N → ℝ)} (hU : U ⊆ simpleEnsembleLocus hP) :
    AnalyticOnNhd ℝ
      (fun q => anchoredGapRatioMap (sortedEnsembleSpectrum hP q) anchor clock ι) U := by
  intro θ hθ
  have hne :
      sortedEnsembleSpectrum hP θ clock - sortedEnsembleSpectrum hP θ anchor ≠ 0 := by
    intro h
    exact hac ((injective_sortedEnsembleSpectrum hP (hU hθ)) (sub_eq_zero.mp h)).symm
  refine analyticAt_pi_iff.mpr fun k => ?_
  have hnum :
      AnalyticAt ℝ
        (fun q : Fin N → ℝ =>
          sortedEnsembleSpectrum hP q (ι k) - sortedEnsembleSpectrum hP q anchor) θ :=
    (analyticAt_sortedEnsembleSpectrum hP (hU hθ) (ι k)).sub
      (analyticAt_sortedEnsembleSpectrum hP (hU hθ) anchor)
  have hden :
      AnalyticAt ℝ
        (fun q : Fin N → ℝ =>
          sortedEnsembleSpectrum hP q clock - sortedEnsembleSpectrum hP q anchor) θ :=
    (analyticAt_sortedEnsembleSpectrum hP (hU hθ) clock).sub
      (analyticAt_sortedEnsembleSpectrum hP (hU hθ) anchor)
  exact hnum.div hden hne

/-- **Extremality of the sorted gap map.**  Almost every parameter of a preconnected open piece of
the simple-spectrum locus is not simultaneously very well approximable in the rescaled anchored
gaps. -/
theorem theoremA_sortedGap [NeZero N] (hn : 0 < n) (hP : ∀ a, (P a).IsHermitian)
    (hS : SpectrumEscapesAffineRelations (Set.range (spectralEnsembleMatrix P)))
    {anchor : Fin D} {ι : Fin n → Fin D} (hι : Function.Injective ι)
    (hanchor : ∀ k, ι k ≠ anchor) {scale : ℝ} (hscale : scale ≠ 0)
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUsimple : U ⊆ simpleEnsembleLocus hP) :
    volume {x ∈ U |
      KleinbockMargulis.VWA fun k =>
        anchoredGapMap scale (sortedEnsembleSpectrum hP x) anchor ι k} = 0 := by
  have hfamily : realAffineMatrix 0 P = spectralEnsembleMatrix P :=
    funext fun θ => realAffineMatrix_zero_eq_spectralEnsembleMatrix P θ
  refine theoremA_anchoredGap hn 0 P (by rw [hfamily]; exact hS) hι hanchor hscale hU hUc hUne
    (fun q => sortedEnsembleSpectrum hP q)
    (fun q hq => injective_sortedEnsembleSpectrum hP (hUsimple hq)) ?_
    (analyticOnNhd_anchoredGapMap hP hscale anchor ι hUsimple)
  intro q _ i
  rw [realAffineMatrix_zero_eq_spectralEnsembleMatrix]
  exact matrixCharpolyRelation_sortedEnsembleSpectrum hP q i

/-- **Extremality of the sorted gap-ratio map.** -/
theorem theoremA_sortedGapRatio [NeZero N] (hn : 0 < n) (hP : ∀ a, (P a).IsHermitian)
    (hS : SpectrumEscapesRealRelations (Set.range (spectralEnsembleMatrix P)))
    {anchor clock : Fin D} {ι : Fin n → Fin D} (hι : Function.Injective ι)
    (hanchor : ∀ k, ι k ≠ anchor) (hclock : ∀ k, ι k ≠ clock) (hac : anchor ≠ clock)
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUsimple : U ⊆ simpleEnsembleLocus hP) :
    volume {x ∈ U |
      KleinbockMargulis.VWA fun k =>
        anchoredGapRatioMap (sortedEnsembleSpectrum hP x) anchor clock ι k} = 0 := by
  have hfamily : realAffineMatrix 0 P = spectralEnsembleMatrix P :=
    funext fun θ => realAffineMatrix_zero_eq_spectralEnsembleMatrix P θ
  refine theoremA_gapRatio hn 0 P (by rw [hfamily]; exact hS) hι hanchor hclock hac hU hUc hUne
    (fun q => sortedEnsembleSpectrum hP q)
    (fun q hq => injective_sortedEnsembleSpectrum hP (hUsimple hq)) ?_
    (analyticOnNhd_anchoredGapRatioMap hP hac ι hUsimple)
  intro q _ i
  rw [realAffineMatrix_zero_eq_spectralEnsembleMatrix]
  exact matrixCharpolyRelation_sortedEnsembleSpectrum hP q i

end

end GaloisForLFunctions.HTGeometry
