import GaloisForLFunctions.RHTower.HedenmalmStokesFourthTraceCurvatureBudgetBand

/-!
# Curvature-tail finite-ceiling law

P-G146 leaves only the positive and negative high-frequency tails of the curvature-normalized
Route P flux.  This module uses functional-equation reflection and Schwarz reality to identify the
positive right-strip tail with the positive-frequency centered source trace.

The resulting obstruction is stronger than a missing sign: after any verified central band, mere
finite upper boundedness of the curvature-normalized positive tail is equivalent to RH.  At the
unconditional fourth-trace threshold `233 / 20`, false RH therefore forces arbitrarily large
positive curvature-tail spikes.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Functional-equation reflection followed by Schwarz conjugation transports the centered
upper-strip source trace to the positive-frequency right-strip completed flux. -/
theorem seamFluxCochain_rightSchwarz_re_eq_continuedPrimeArchSourceRelativeTrace_im
    {z : ℂ} (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    (seamFluxCochain (1 / 2 + (starRingEnd ℂ) z * I)).re =
      (continuedPrimeArchSourceRelativeTrace z).im := by
  let sL : ℂ := 1 / 2 + z * I
  let sR : ℂ := 1 / 2 + (starRingEnd ℂ) z * I
  have hsLre : sL.re = (1 / 2 : ℝ) - z.im := by
    norm_num [sL, mul_re]
    ring
  have hsLpos : 0 < sL.re := by
    rw [hsLre]
    linarith
  have hsL1 : sL ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    rw [hsLre, one_re] at hre
    linarith
  have hsource :
      continuedPrimeArchSourceRelativeTrace z = -I * seamFluxCochain sL := by
    rw [continuedPrimeArchSourceRelativeTrace]
    change -I * (infinitePrimeFlux sL - logDeriv archFactor sL) = _
    rw [← seamFluxCochain_eq_continuedPrime_add_archimedean hsLpos hsL1 hzeta]
  have hcoord : sR = (starRingEnd ℂ) (1 - sL) := by
    apply Complex.ext
    · simp [sL, sR, mul_re]; ring
    · simp [sL, sR, mul_im]
  have hreflect :
      seamFluxCochain sR = -(starRingEnd ℂ) (seamFluxCochain sL) := by
    rw [hcoord, seamFluxCochain_conj, seamFluxCochain_reciprocity]
    simp
  change (seamFluxCochain sR).re =
    (continuedPrimeArchSourceRelativeTrace z).im
  rw [hreflect, hsource]
  simp [mul_im]

/-- Finite upper boundedness of the curvature-normalized right-strip positive-frequency tail.
No sign or sharp central-curvature allowance is required. -/
def HedenmalmCurvatureNormalizedRightPositiveTailBoundedAbove (R : ℝ) : Prop :=
  ∃ C : ℝ, ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → R < s.im →
    riemannZeta s ≠ 0 →
      (hedenmalmCurvatureNormalizedSeamFlux s).re ≤ C

/-- A verified central band plus any finite upper ceiling on the positive-frequency
curvature-normalized tail proves RH.  Conversely RH supplies such a ceiling from the sharp P-G144
budget and the bounded critical-strip aperture. -/
theorem hedenmalmCurvatureNormalizedRightPositiveTailBoundedAbove_iff_rh_of_verifiedHeight
    (H R : ℝ) (hverified : RHVerifiedThrough H) (hband : R + 1 / 2 ≤ H) :
    HedenmalmCurvatureNormalizedRightPositiveTailBoundedAbove R ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨C, hC⟩
    apply riemannHypothesis_of_verifiedHeight_and_positiveFrequencyAboveImBoundedAbove
      H R hverified hband
    refine ⟨C, ?_⟩
    intro z hzIm hzHalf hzRe hzeta
    let sL : ℂ := 1 / 2 + z * I
    let sR : ℂ := 1 / 2 + (starRingEnd ℂ) z * I
    have hsLre : sL.re = (1 / 2 : ℝ) - z.im := by
      norm_num [sL, mul_re]
      ring
    have hsRre : sR.re = (1 / 2 : ℝ) + z.im := by
      norm_num [sR, mul_re]
    have hsRim : sR.im = z.re := by
      norm_num [sR, mul_im]
    have hsLpos : 0 < sL.re := by
      rw [hsLre]
      linarith
    have hsL1 : sL ≠ 1 := by
      intro hs
      have hre := congrArg Complex.re hs
      rw [hsLre, one_re] at hre
      linarith
    have hsRhalf : 1 / 2 < sR.re := by
      rw [hsRre]
      linarith
    have hsRone : sR.re < 1 := by
      rw [hsRre]
      linarith
    have hsRfreq : R < sR.im := by
      rw [hsRim]
      exact hzRe
    have hcoord : sR = (starRingEnd ℂ) (1 - sL) := by
      apply Complex.ext
      · simp [sL, sR, mul_re]; ring
      · simp [sL, sR, mul_im]
    have hxiL : xi sL ≠ 0 :=
      (xi_eq_zero_iff hsLpos hsL1).not.mpr (by simpa only [sL] using hzeta)
    have hxiR : xi sR ≠ 0 := by
      rw [hcoord, xi_conj, xi_one_sub]
      exact (map_ne_zero (starRingEnd ℂ)).2 hxiL
    have hsRpos : 0 < sR.re := lt_trans (by norm_num) hsRhalf
    have hsR1 : sR ≠ 1 := by
      intro hs
      have hre := congrArg Complex.re hs
      rw [one_re] at hre
      linarith
    have hzetaR : riemannZeta sR ≠ 0 :=
      (xi_eq_zero_iff hsRpos hsR1).not.mp hxiR
    have hnormalized := hC sR hsRhalf hsRone hsRfreq hzetaR
    have hraw_le_normalized :
        (seamFluxCochain sR).re ≤
          (hedenmalmCurvatureNormalizedSeamFlux sR).re := by
      have him := deriv_seamFluxCochain_one_half_im_eq_zero
      rw [hedenmalmCurvatureNormalizedSeamFlux, hedenmalmCurvatureNormalizedFlux]
      simp only [Complex.sub_re, Complex.mul_re, Complex.sub_im]
      rw [him, mul_zero, sub_zero]
      norm_num
      nlinarith [deriv_seamFluxCochain_one_half_re_neg]
    rw [← seamFluxCochain_rightSchwarz_re_eq_continuedPrimeArchSourceRelativeTrace_im
      hzIm hzHalf hzeta]
    exact hraw_le_normalized.trans hnormalized
  · intro hRH
    have hbudget : HedenmalmCurvatureNormalizedRightBudget :=
      hedenmalmCurvatureNormalizedRightBudget_iff_riemannHypothesis.mpr hRH
    refine ⟨-(1 / 2) * (deriv seamFluxCochain (1 / 2)).re, ?_⟩
    intro s hhalf hone _hfreq hzeta
    have hsharp := hbudget s hhalf hone hzeta
    have hx : 0 < s.re - 1 / 2 := sub_pos.mpr hhalf
    have hxUpper : s.re - 1 / 2 < 1 / 2 := by linarith
    exact hsharp.trans (by
      nlinarith [deriv_seamFluxCochain_one_half_re_neg])

/-- At the strongest unconditional fourth-trace prefix currently present in the source corpus,
mere finite upper boundedness of the positive curvature tail is exactly RH. -/
theorem hedenmalmCurvatureNormalizedRightPositiveTailBoundedAbove_twoHundredThirtyThree_twentieths_iff_rh :
    HedenmalmCurvatureNormalizedRightPositiveTailBoundedAbove (233 / 20) ↔
      RiemannHypothesis := by
  exact hedenmalmCurvatureNormalizedRightPositiveTailBoundedAbove_iff_rh_of_verifiedHeight
    (243 / 20) (233 / 20) rhVerifiedThrough_twoHundredFortyThree_twentieths (by norm_num)

/-- **Positive curvature-tail failure law.**  If RH is false, the positive-frequency
curvature-normalized tail beyond `233 / 20` exceeds every finite ceiling. -/
theorem exists_hedenmalmCurvatureNormalizedSeamFlux_re_gt_above_twoHundredThirtyThree_twentieths_of_not_rh
    (hnot : ¬ RiemannHypothesis) (C : ℝ) :
    ∃ s : ℂ, 1 / 2 < s.re ∧ s.re < 1 ∧ 233 / 20 < s.im ∧
      riemannZeta s ≠ 0 ∧
        C < (hedenmalmCurvatureNormalizedSeamFlux s).re := by
  by_contra h
  apply hnot
  apply hedenmalmCurvatureNormalizedRightPositiveTailBoundedAbove_twoHundredThirtyThree_twentieths_iff_rh.mp
  refine ⟨C, ?_⟩
  intro s hhalf hone hfreq hzeta
  exact le_of_not_gt fun hgt => h ⟨s, hhalf, hone, hfreq, hzeta, hgt⟩

/-- The strongest unconditional fourth-trace prefix reduces the completed prime--Gamma endpoint
to one common lower bound on a countable dense tail strictly above `233 / 20`. -/
theorem completedPrimeGammaGaussianRatPositiveFrequencyAboveReBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh :
    CompletedPrimeGammaGaussianRatPositiveFrequencyAboveReBoundedBelow (233 / 20) ↔
      RiemannHypothesis := by
  constructor
  · intro hrat
    exact
      (continuedPrimeArchPositiveFrequencyAboveImBoundedAbove_iff_rh_of_verifiedHeight
        (243 / 20) (233 / 20) rhVerifiedThrough_twoHundredFortyThree_twentieths
        (by norm_num)).mp
        (continuedPrimeArchPositiveFrequencyAboveImBoundedAbove_of_gaussianRatReBoundedBelow
          (233 / 20) hrat)
  · intro hRH
    obtain ⟨L, hL⟩ :=
      completedPrimeGammaGaussianRatLeftHalfBoundedBelow_of_riemannHypothesis hRH
    exact ⟨L, fun q hqpos hqhalf _hqhigh hqzeta => hL q hqpos hqhalf hqzeta⟩

/-- At the fourth-trace threshold, countable completed-flux boundedness and finite boundedness of
the curvature-normalized right tail are the same RH-bearing condition. -/
theorem completedPrimeGammaGaussianRatPositiveFrequencyAboveReBoundedBelow_twoHundredThirtyThree_twentieths_iff_curvatureTailBoundedAbove :
    CompletedPrimeGammaGaussianRatPositiveFrequencyAboveReBoundedBelow (233 / 20) ↔
      HedenmalmCurvatureNormalizedRightPositiveTailBoundedAbove (233 / 20) :=
  completedPrimeGammaGaussianRatPositiveFrequencyAboveReBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh.trans
    hedenmalmCurvatureNormalizedRightPositiveTailBoundedAbove_twoHundredThirtyThree_twentieths_iff_rh.symm

/-- Threshold consolidation: the smaller fourth-trace tail has exactly the same content as the
older source-pure tail above four. -/
theorem completedPrimeGammaGaussianRatPositiveFrequencyAboveReBoundedBelow_twoHundredThirtyThree_twentieths_iff_four :
    CompletedPrimeGammaGaussianRatPositiveFrequencyAboveReBoundedBelow (233 / 20) ↔
      CompletedPrimeGammaGaussianRatPositiveFrequencyAboveReBoundedBelow 4 :=
  completedPrimeGammaGaussianRatPositiveFrequencyAboveReBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh.trans
    completedPrimeGammaGaussianRatPositiveFrequencyAboveReBoundedBelow_four_iff_rh.symm

/-- Positive countable failure law at the fourth-trace threshold: false RH drives admissible
Gaussian-rational completed flux below every proposed common lower bound. -/
theorem exists_gaussianRat_completedPrimeGammaFlux_re_lt_above_twoHundredThirtyThree_twentieths_of_not_rh
    (hnot : ¬ RiemannHypothesis) :
    ∀ L : ℝ, ∃ q : ℚ × ℚ, 0 < (gaussianRatPoint q).re ∧
      (gaussianRatPoint q).re < 1 / 2 ∧ 233 / 20 < (gaussianRatPoint q).im ∧
      riemannZeta (gaussianRatPoint q) ≠ 0 ∧
        (completedPrimeGammaFlux (gaussianRatPoint q)).re < L := by
  intro L
  by_contra hescape
  push Not at hescape
  apply hnot
  exact
    completedPrimeGammaGaussianRatPositiveFrequencyAboveReBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh.mp
      ⟨L, fun q hqpos hqhalf hqhigh hqzeta =>
        hescape q hqpos hqhalf hqhigh hqzeta⟩

end

end RHTower
