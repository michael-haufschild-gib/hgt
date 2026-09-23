import GaloisForLFunctions.RHTower.HedenmalmStokesCurvatureBudgetCentralBand
import GaloisForLFunctions.RHTower.PrimeArchVerifiedHeightAccretivity
import GaloisForLFunctions.RHTower.XiFourthTraceExtendedCriticalLineBand

/-!
# Fourth-trace extension of the curvature-normalized Stokes band

P-G145 transports endpoint-quartet accretivity to the curvature-normalized Route P budget on
`|Im s| <= 218 / 25`.  A stronger source theorem was already available in a different coordinate:
the fourth reciprocal trace puts every off-line Xi zero above squared height `2365 / 16`.

This module converts that fourth-trace exclusion into an unconditional verified-height certificate
through `243 / 20`, transfers it to completed-flux passivity, and enlarges the closed Route P slab
to `|Im s| <= 233 / 20`.  The remaining RH-equivalent tail begins strictly later.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- The fourth reciprocal-trace source budget verifies RH through the rational height `243 / 20`.
This is a theorem certificate, not an imported zero computation. -/
theorem rhVerifiedThrough_twoHundredFortyThree_twentieths :
    RHVerifiedThrough (243 / 20) := by
  intro rho hzero hre0 hre1 him0 himUpper
  let rhoSupport : XiDivisorSupport :=
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
  let q : XiZeroCopy := by
    have hpos := xi_divisor_pos_on_support rhoSupport
    have hn : 0 < Int.toNat
        ((MeromorphicOn.divisor xi Set.univ) (rhoSupport : ℂ)) := by
      omega
    exact ⟨rhoSupport, ⟨0, hn⟩⟩
  have hsq : (q.1 : ℂ).im ^ (2 : ℕ) < 2365 / 16 := by
    change rho.im ^ (2 : ℕ) < 2365 / 16
    nlinarith [sq_pos_of_pos him0]
  have hline := xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q hsq
  simpa only [q, rhoSupport] using hline

/-- A verified Xi height transports directly to raw completed-flux passivity on the corresponding
frequency band. -/
theorem seamFluxCochain_re_nonpos_of_verifiedHeightBand
    (H R : ℝ) (hverified : RHVerifiedThrough H) (hband : R + 1 / 2 ≤ H)
    {s : ℂ} (hhalf : 1 / 2 < s.re) (hfreq : |s.im| ≤ R) :
    (seamFluxCochain s).re ≤ 0 := by
  let a : ℝ := s.re - 1 / 2
  let b : ℝ := s.im
  let z : ℂ := (b : ℂ) - (a : ℂ) * I
  let zplus : ℂ := (b : ℂ) + (a : ℂ) * I
  have ha : 0 < a := by
    dsimp only [a]
    linarith
  have hzplusIm : 0 < zplus.im := by
    simp only [zplus, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
      zero_add, zero_mul, mul_one]
    simpa using ha
  have hzplusRe : |zplus.re| ≤ R := by
    simpa only [zplus, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero, b] using hfreq
  have hXiPlus : XiC zplus ≠ 0 :=
    XiC_ne_zero_of_upperHalf_verifiedHeightBand
      H R hverified hband zplus hzplusIm hzplusRe
  have hconj : (starRingEnd ℂ) zplus = z := by
    apply Complex.ext <;>
      simp [z, zplus, mul_re, mul_im]
  have hXi : XiC z ≠ 0 := by
    simpa only [hconj] using XiC_ne_zero_conj hXiPlus
  have htrace := xiRelativeResolventTrace_im_nonpos_on_verifiedHeightBand
    H R hverified hband zplus hzplusIm hzplusRe
  have htraceLower : 0 ≤ (xiRelativeResolventTrace z).im := by
    have hreflect := xiRelativeResolventTrace_conj z
    have hconjBack : (starRingEnd ℂ) z = zplus := by
      apply Complex.ext <;>
        simp [z, zplus, mul_re, mul_im]
    rw [hconjBack] at hreflect
    rw [hreflect] at htrace
    simp only [Complex.conj_im] at htrace
    linarith
  have hcoord : (1 / 2 : ℂ) + z * I = s := by
    apply Complex.ext <;>
      simp [z, a, b, mul_re, mul_im]
  rw [xiRelativeResolventTrace_eq_completedFlux hXi, hcoord] at htraceLower
  simp only [mul_im, neg_re, neg_im, I_re, I_im, zero_mul, neg_zero] at htraceLower
  linarith

/-- Curvature normalization preserves every verified-height completed-flux band. -/
theorem hedenmalmCurvatureNormalizedSeamFlux_budget_of_verifiedHeightBand
    (H R : ℝ) (hverified : RHVerifiedThrough H) (hband : R + 1 / 2 ≤ H)
    {s : ℂ} (hhalf : 1 / 2 < s.re) (hfreq : |s.im| ≤ R) :
    (hedenmalmCurvatureNormalizedSeamFlux s).re ≤
      -(s.re - 1 / 2) * (deriv seamFluxCochain (1 / 2)).re := by
  have hraw := seamFluxCochain_re_nonpos_of_verifiedHeightBand
    H R hverified hband hhalf hfreq
  have him := deriv_seamFluxCochain_one_half_im_eq_zero
  rw [hedenmalmCurvatureNormalizedSeamFlux, hedenmalmCurvatureNormalizedFlux]
  simp only [Complex.sub_re, Complex.mul_re, Complex.sub_im]
  rw [him, mul_zero, sub_zero]
  norm_num
  linarith

/-- The fourth-trace source theorem closes the Route P budget on
`|Im s| <= 233 / 20`. -/
theorem hedenmalmCurvatureNormalizedSeamFlux_budget_twoHundredThirtyThree_twentieths
    {s : ℂ} (hhalf : 1 / 2 < s.re) (hfreq : |s.im| ≤ 233 / 20) :
    (hedenmalmCurvatureNormalizedSeamFlux s).re ≤
      -(s.re - 1 / 2) * (deriv seamFluxCochain (1 / 2)).re := by
  exact hedenmalmCurvatureNormalizedSeamFlux_budget_of_verifiedHeightBand
    (243 / 20) (233 / 20) rhVerifiedThrough_twoHundredFortyThree_twentieths
    (by norm_num) hhalf hfreq

/-- A verified-height band reduces the global curvature budget exactly to its two exterior tails. -/
theorem hedenmalmCurvatureNormalizedRightTailBudget_iff_rightBudget_of_verifiedHeightBand
    (H R : ℝ) (hverified : RHVerifiedThrough H) (hband : R + 1 / 2 ≤ H) :
    HedenmalmCurvatureNormalizedRightTailBudget R ↔
      HedenmalmCurvatureNormalizedRightBudget := by
  constructor
  · intro htail s hhalf hone hzeta
    by_cases hhigh : R < |s.im|
    · exact htail s hhalf hone hhigh hzeta
    · exact hedenmalmCurvatureNormalizedSeamFlux_budget_of_verifiedHeightBand
        H R hverified hband hhalf (le_of_not_gt hhigh)
  · intro hglobal s hhalf hone _hhigh hzeta
    exact hglobal s hhalf hone hzeta

/-- **Fourth-trace tail localization.**  Only frequencies beyond `233 / 20` retain RH-bearing
content in the curvature-normalized Route P budget. -/
theorem hedenmalmCurvatureNormalizedRightTailBudget_twoHundredThirtyThree_twentieths_iff_rh :
    HedenmalmCurvatureNormalizedRightTailBudget (233 / 20) ↔
      RiemannHypothesis := by
  rw [hedenmalmCurvatureNormalizedRightTailBudget_iff_rightBudget_of_verifiedHeightBand
      (243 / 20) (233 / 20) rhVerifiedThrough_twoHundredFortyThree_twentieths
      (by norm_num),
    hedenmalmCurvatureNormalizedRightBudget_iff_riemannHypothesis]

/-- Closed fourth-trace specialization of the signed positive-frequency prime--Gamma tail. -/
theorem continuedPrimeArchPositiveFrequencyAbove_twoHundredThirtyThree_twentieths_iff_rh :
    ContinuedPrimeArchPositiveFrequencyAbove (233 / 20) ↔ RiemannHypothesis :=
  continuedPrimeArchPositiveFrequencyAbove_iff_rh_of_verifiedHeight
    (243 / 20) (233 / 20) rhVerifiedThrough_twoHundredFortyThree_twentieths
    (by norm_num)

/-- Closed fourth-trace specialization of the finite-ceiling positive-frequency tail. -/
theorem continuedPrimeArchPositiveFrequencyAboveImBoundedAbove_twoHundredThirtyThree_twentieths_iff_rh :
    ContinuedPrimeArchPositiveFrequencyAboveImBoundedAbove (233 / 20) ↔
      RiemannHypothesis :=
  continuedPrimeArchPositiveFrequencyAboveImBoundedAbove_iff_rh_of_verifiedHeight
    (243 / 20) (233 / 20) rhVerifiedThrough_twoHundredFortyThree_twentieths
    (by norm_num)

/-- False RH forces the fourth-trace positive-frequency tail above every finite ceiling. -/
theorem exists_continuedPrimeArchSource_im_gt_above_twoHundredThirtyThree_twentieths_of_not_rh
    (hnot : ¬ RiemannHypothesis) (C : ℝ) :
    ∃ z : ℂ, 0 < z.im ∧ z.im < 1 / 2 ∧ 233 / 20 < z.re ∧
      riemannZeta (1 / 2 + z * I) ≠ 0 ∧
        C < (continuedPrimeArchSourceRelativeTrace z).im :=
  exists_continuedPrimeArchSource_im_gt_above_of_not_rh_verifiedHeight
    (243 / 20) (233 / 20) rhVerifiedThrough_twoHundredFortyThree_twentieths
    (by norm_num) hnot C

end

end RHTower
