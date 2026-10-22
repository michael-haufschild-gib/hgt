import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureBoundaryAliasPositiveSaving
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureFirstOrderWindingAsymptotic
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureSevenTenthsAsymptoticReceiver

/-!
# Boundary-variance source majorant: exact 75% receiver

The positive boundary-alias selector gives an infinite translated Plemelj majorant with a
normalized variance saving.  One extra lattice layer absorbs every phase in `[0,1]`.  This file
connects any `21/100` ceiling for that explicit source majorant to the exact multiplicity census
and hence to an eventual three-quarter critical-line bound.

No quantitative source ceiling is assumed silently: it is the sole premise of the terminal
theorem.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- Complete strict-right multiplicity packet, split only to reuse the proved shallow/deep
canonical census. -/
def criticalFeatureCanonicalRightCopyPacket (n : ℕ) : Finset XiZeroCopy :=
  criticalFeatureCanonicalShallowRightCopyPacket n ∪
    criticalFeatureCanonicalDeepRightCopyPacket n

theorem disjoint_criticalFeatureCanonicalShallowRightCopyPacket_deep (n : ℕ) :
    Disjoint (criticalFeatureCanonicalShallowRightCopyPacket n)
      (criticalFeatureCanonicalDeepRightCopyPacket n) := by
  rw [Finset.disjoint_left]
  intro q hshallow hdeep
  have hs := mem_criticalFeatureCanonicalShallowRightCopyPacket.mp hshallow
  have hd := mem_criticalFeatureCanonicalDeepRightCopyPacket.mp hdeep
  linarith [hs.2.2.2, hd.2.2]

theorem card_criticalFeatureCanonicalRightCopyPacket (n : ℕ) :
    (criticalFeatureCanonicalRightCopyPacket n).card =
      (criticalFeatureCanonicalShallowRightCopyPacket n).card +
        (criticalFeatureCanonicalDeepRightCopyPacket n).card := by
  rw [criticalFeatureCanonicalRightCopyPacket,
    Finset.card_union_of_disjoint
      (disjoint_criticalFeatureCanonicalShallowRightCopyPacket_deep n)]

theorem criticalFeatureCanonicalRightCopyPacket_transverse_pos
    {n : ℕ} {q : XiZeroCopy}
    (hq : q ∈ criticalFeatureCanonicalRightCopyPacket n) :
    0 < (I * xiSpectralPoint q).re := by
  rw [criticalFeatureCanonicalRightCopyPacket, Finset.mem_union] at hq
  rcases hq with hshallow | hdeep
  · exact criticalFeatureCanonicalShallowRightCopyPacket_transverse_pos hshallow
  · have hd := mem_criticalFeatureCanonicalDeepRightCopyPacket.mp hdeep
    rw [I_mul_xiSpectralPoint, Complex.sub_re]
    norm_num
    linarith [hd.2.2]

theorem criticalFeatureCanonicalRightCopyPacket_height_le
    {n : ℕ} {q : XiZeroCopy}
    (hq : q ∈ criticalFeatureCanonicalRightCopyPacket n) :
    |(xiSpectralPoint q).re| ≤ n := by
  rw [criticalFeatureCanonicalRightCopyPacket, Finset.mem_union] at hq
  rcases hq with hshallow | hdeep
  · have hs := mem_criticalFeatureCanonicalShallowRightCopyPacket.mp hshallow
    simpa [xiSpectralPoint] using hs.1
  · have hd := mem_criticalFeatureCanonicalDeepRightCopyPacket.mp hdeep
    simpa [xiSpectralPoint] using hd.1

/-- One extra canonical lattice layer retains the translated nearest center and both neighbours
uniformly for every source phase in `[0,1]`. -/
theorem criticalFeatureCanonicalRightCopyPacket_threeCenters_translated
    {n : ℕ} {q : XiZeroCopy} {theta : ℝ}
    (hq : q ∈ criticalFeatureCanonicalRightCopyPacket n)
    (htheta : theta ∈ Icc (-1 : ℝ) 0) :
    round ((xiSpectralPoint q).re - theta) - 1 ∈
        criticalFeatureCanonicalFiveCenterLatticeWindow n ∧
      round ((xiSpectralPoint q).re - theta) ∈
        criticalFeatureCanonicalFiveCenterLatticeWindow n ∧
      round ((xiSpectralPoint q).re - theta) + 1 ∈
        criticalFeatureCanonicalFiveCenterLatticeWindow n := by
  have hx := criticalFeatureCanonicalRightCopyPacket_height_le hq
  have herr := HTGeometry.abs_sub_round_le_half ((xiSpectralPoint q).re - theta)
  rw [abs_le] at hx herr
  have hupperReal :
      ((round ((xiSpectralPoint q).re - theta) : ℤ) : ℝ) < n + 2 := by
    linarith [hx.2, htheta.1, herr.1]
  have hlowerReal :
      -(n : ℝ) - 1 <
        ((round ((xiSpectralPoint q).re - theta) : ℤ) : ℝ) := by
    linarith [hx.1, htheta.2, herr.2]
  have hupperInt :
      round ((xiSpectralPoint q).re - theta) < (n : ℤ) + 2 := by
    exact_mod_cast hupperReal
  have hlowerInt :
      -(n : ℤ) - 1 < round ((xiSpectralPoint q).re - theta) := by
    exact_mod_cast hlowerReal
  simp only [criticalFeatureCanonicalFiveCenterLatticeWindow,
    criticalFeatureCanonicalLatticeWindow, Finset.mem_Icc]
  omega

theorem criticalFeatureCanonicalZeroCount_eq_criticalLine_add_two_mul_rightCopyPacket
    (n : ℕ) :
    criticalFeatureCanonicalZeroCount n =
      criticalFeatureCanonicalCriticalLineCount n +
        2 * (criticalFeatureCanonicalRightCopyPacket n).card := by
  rw [card_criticalFeatureCanonicalRightCopyPacket]
  push_cast
  exact criticalFeatureCanonicalZeroCount_eq_criticalLine_add_two_mul_shallow_deep n

/-- Five-center-indexed version of the variance-saved source majorant. -/
def criticalFeatureCanonicalBoundaryVarianceFiveCenterSourceMajorant (n : ℕ) : ℝ :=
  criticalFeatureCanonicalBoundaryVariancePlemeljSourceMajorant (n + 1)

/-- Pointwise domination of the translated five-center Plemelj covariance by the new source
majorant. -/
theorem criticalFeatureTranslatedFiveCenterPlemelj_lt_boundaryVarianceSourceMajorant
    (n : ℕ) :
    criticalFeatureTranslatedPoleGammaPlemeljCovariance
        (-(criticalFeatureCompactBoundaryVarianceSavingPhase (n + 1)))
        (criticalFeatureCanonicalFiveCenterLatticeWindow n) <
      criticalFeatureCanonicalBoundaryVarianceFiveCenterSourceMajorant n := by
  simpa only [criticalFeatureCanonicalFiveCenterLatticeWindow,
    criticalFeatureCanonicalBoundaryVarianceFiveCenterSourceMajorant] using
    criticalFeatureTranslatedPoleGammaPlemeljCovariance_lt_boundaryVarianceSourceMajorant
      (n + 1)

theorem canonicalTranslatedFiveCenterPlemelj_ceiling_of_boundaryVarianceSourceMajorant
    {c : ℝ}
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      criticalFeatureCanonicalBoundaryVarianceFiveCenterSourceMajorant c) :
    CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeatureTranslatedPoleGammaPlemeljCovariance
        (-(criticalFeatureCompactBoundaryVarianceSavingPhase (n + 1)))
        (criticalFeatureCanonicalFiveCenterLatticeWindow n)) c := by
  intro eps heps
  filter_upwards [hsource eps heps] with n hn
  exact
    (criticalFeatureTranslatedFiveCenterPlemelj_lt_boundaryVarianceSourceMajorant n).le.trans hn

/-- Source-majorant ceiling transfers to the actual translated corrected HCF budget. -/
theorem canonicalTranslatedFiveCenterCorrectedBudget_ceiling_of_boundaryVarianceSourceMajorant
    {c : ℝ}
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      criticalFeatureCanonicalBoundaryVarianceFiveCenterSourceMajorant c) :
    CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget
        (-(criticalFeatureCompactBoundaryVarianceSavingPhase (n + 1)))
        (criticalFeatureCanonicalFiveCenterLatticeWindow n)) c := by
  let theta : ℕ → ℝ := fun n =>
    -(criticalFeatureCompactBoundaryVarianceSavingPhase (n + 1))
  let K : ℕ → Finset ℤ := criticalFeatureCanonicalFiveCenterLatticeWindow
  have hplemelj : CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeatureTranslatedPoleGammaPlemeljCovariance
        (theta n) (K n)) c := by
    simpa only [theta, K] using
      canonicalTranslatedFiveCenterPlemelj_ceiling_of_boundaryVarianceSourceMajorant hsource
  have hdiff := tendsto_translatedCorrectedBudget_sub_sourceCovariance_div
    theta K criticalFeatureCanonicalZeroCount
    eventually_criticalFeatureCanonicalZeroCount_pos
    tendsto_card_criticalFeatureCanonicalFiveCenterLatticeWindow_div_zeroCount
  exact
    (criticalFeatureCanonicalAsymptoticUpper_iff_of_sub_div_tendsto_zero hdiff).mpr hplemelj

/-- Exact pointwise receiver at the variance-saving source phase. -/
theorem three_quarters_line_of_boundaryVarianceTranslatedBudget
    (n : ℕ)
    (hbudget :
      criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget
          (-(criticalFeatureCompactBoundaryVarianceSavingPhase (n + 1)))
          (criticalFeatureCanonicalFiveCenterLatticeWindow n) ≤
        (15872 / 21125 : ℝ) * criticalFeatureCanonicalZeroCount n) :
    3 * criticalFeatureCanonicalZeroCount n / 4 ≤
      criticalFeatureCanonicalCriticalLineCount n := by
  let theta : ℝ := -(criticalFeatureCompactBoundaryVarianceSavingPhase (n + 1))
  have hphase := criticalFeatureCompactBoundaryVarianceSavingPhase_mem (n + 1)
  have htheta : theta ∈ Icc (-1 : ℝ) 0 := by
    dsimp only [theta]
    constructor <;> linarith [hphase.1, hphase.2]
  apply three_quarters_line_of_reflectedDirectThreeCenter_translatedLatticeBudget
    theta (criticalFeatureCanonicalFiveCenterLatticeWindow n)
      (criticalFeatureCanonicalRightCopyPacket n)
  · intro q hq
    exact criticalFeatureCanonicalRightCopyPacket_transverse_pos hq
  · intro q hq
    exact criticalFeatureCanonicalRightCopyPacket_threeCenters_translated hq htheta
  · exact criticalFeatureCanonicalZeroCount_eq_criticalLine_add_two_mul_rightCopyPacket n
  · simpa only [theta] using hbudget

/-- A `21/100` ceiling for the explicit zero-independent variance-saved source majorant forces
at least three quarters of all canonical zeros onto the critical line, eventually. -/
theorem eventually_three_quarters_line_of_boundaryVarianceSourceMajorant_twentyOneHundred
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      criticalFeatureCanonicalBoundaryVarianceFiveCenterSourceMajorant (21 / 100)) :
    ∀ᶠ n : ℕ in atTop,
      3 * criticalFeatureCanonicalZeroCount n / 4 ≤
        criticalFeatureCanonicalCriticalLineCount n := by
  have hcorrected :=
    canonicalTranslatedFiveCenterCorrectedBudget_ceiling_of_boundaryVarianceSourceMajorant
      hsource
  have hgap : (0 : ℝ) < 15872 / 21125 - 21 / 100 := by norm_num
  have hbudget := hcorrected (15872 / 21125 - 21 / 100) hgap
  filter_upwards [hbudget] with n hn
  apply three_quarters_line_of_boundaryVarianceTranslatedBudget n
  have hcoeff : (21 / 100 : ℝ) + (15872 / 21125 - 21 / 100) =
      15872 / 21125 := by norm_num
  simpa only [hcoeff] using hn

/-- Asymptotic-density form of the same exact receiver. -/
theorem criticalFeatureCanonicalCriticalLineCount_threeQuarters_lower_of_boundaryVarianceSourceMajorant
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      criticalFeatureCanonicalBoundaryVarianceFiveCenterSourceMajorant (21 / 100)) :
    CriticalFeatureCanonicalAsymptoticLower
      criticalFeatureCanonicalCriticalLineCount (3 / 4) := by
  intro eps heps
  have hthree :=
    eventually_three_quarters_line_of_boundaryVarianceSourceMajorant_twentyOneHundred hsource
  filter_upwards [hthree] with n hn
  have hN : 0 ≤ criticalFeatureCanonicalZeroCount n := by
    dsimp only [criticalFeatureCanonicalZeroCount]
    exact_mod_cast xiZeroCount_nonneg (n : ℝ)
  nlinarith

end

end RHTower
