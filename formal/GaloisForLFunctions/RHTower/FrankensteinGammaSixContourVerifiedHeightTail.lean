import GaloisForLFunctions.RHTower.FrankensteinGammaSixGuinandWeilContourCarrier
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmStokesFourthTraceCurvatureBudgetBand

/-!
# Frankenstein Gamma-six contour verified-height tail

This module splices the exact Gamma-six Guinand--Weil contour carrier with an independent fourth
reciprocal-trace exclusion. The reciprocal trace proves every Xi copy through height
`243 / 20` is critical, so every admissible source contour in that band is unconditionally
subexponential. Consequently the global contour criterion is reduced exactly to contours above
that height.

The remaining producer is now a high-height continued prime--Gamma cancellation theorem. Low
frequencies, divisor multiplicity, functional-equation orientation, and finite phase cancellation
are already discharged by separate corpus mechanisms.
-/

open Complex Filter Topology intervalIntegral Set

namespace RHTower

noncomputable section

/-- The fourth reciprocal trace discharges every admissible Gamma-six source contour whose
height radius lies in the unconditionally verified Xi band. -/
theorem sourceHorizontalGammaSixSymmetricPrimeArchContourSubexponential_of_radius_le_verified
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hRverified : R ≤ 243 / 20)
    (hadm : XiSymmetricRectangleExplicitAdmissible R c) :
    SourceHorizontalGammaSixSymmetricPrimeArchContourSubexponential R c := by
  apply (sourceHorizontalGammaSixSymmetricPrimeArchContourSubexponential_iff
    hR hc hadm).2
  intro q hq
  apply xiZeroCopy_re_eq_half_of_verifiedThrough_of_abs_im_le
    (243 / 20) rhVerifiedThrough_twoHundredFortyThree_twentieths q
  have hpoint := (mem_xiZeroCopyClosedRectangle.mp hq)
  obtain ⟨hqre, _hqim⟩ := Complex.mem_reProdIm.mp hpoint
  have hre : (symmetricRectangleLower R c).re ≤
      (symmetricRectangleUpper R c).re := by
    simp [symmetricRectangleLower, symmetricRectangleUpper]
    linarith
  rw [Set.uIcc_of_le hre] at hqre
  have habs : |(xiSpectralPoint q).re| ≤ R := by
    rw [abs_le]
    simpa [symmetricRectangleLower, symmetricRectangleUpper] using hqre
  rw [← xiSpectralPoint_re_eq]
  exact habs.trans hRverified

/-- Only source contours beyond a prescribed height radius retain unresolved content. -/
def SourceHorizontalGammaSixSymmetricPrimeArchContourHighTailSubexponential
    (H : ℝ) : Prop :=
  ∀ (R c : ℝ), H < R → 0 < c → c < 1 / 2 →
    XiSymmetricRectangleExplicitAdmissible R c →
    SourceHorizontalGammaSixSymmetricPrimeArchContourSubexponential R c

/-- Fourth-trace verification turns the global contour criterion into a pure high-height source
tail criterion. This is the exact splice point for D2/T high-frequency arithmetic estimates. -/
theorem sourceHorizontalGammaSixSymmetricPrimeArchContourHighTailSubexponential_iff_rh :
    SourceHorizontalGammaSixSymmetricPrimeArchContourHighTailSubexponential (243 / 20) ↔
      RiemannHypothesis := by
  constructor
  · intro htail
    apply
      riemannHypothesis_iff_forall_sourceHorizontalGammaSixSymmetricPrimeArchContourSubexponential.mpr
    intro R c hR hc hchalf hadm
    by_cases hhigh : 243 / 20 < R
    · exact htail R c hhigh hc hchalf hadm
    · exact sourceHorizontalGammaSixSymmetricPrimeArchContourSubexponential_of_radius_le_verified
        hR hc (le_of_not_gt hhigh) hadm
  · intro hRH R c hR hc hchalf hadm
    exact
      riemannHypothesis_iff_forall_sourceHorizontalGammaSixSymmetricPrimeArchContourSubexponential.mp
        hRH R c (by linarith) hc hchalf hadm

end

end RHTower
