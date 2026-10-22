import GaloisForLFunctions.RHTower.XiWeilHardyCriticalLocusPoissonReserve
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmStokesFourthTraceCurvatureBudgetBand

/-!
# Critical-locus reserve on source-certified verified-height bands

The fourth reciprocal-trace source budget proves a zero-location certificate through height
`243 / 20`, without imported numerical zero data.  The generic verified-height resolvent theorem
transfers this to the centered frequency band `|Re z| ≤ 233 / 20`.

This module applies that stronger corpus certificate after deleting the entire critical fixed
locus.  Consequently every free reflection orbit remains anti-Herglotz through `233 / 20`, source
dissipation pays the complete critical-line Poisson trace there, and the remaining exact RH
obligation begins only above that positive frequency.
-/

open Complex Set
open scoped BigOperators

namespace RHTower

noncomputable section

set_option maxHeartbeats 800000 in
/-- Abstract fixed-locus deletion: if every line-conjugate pair is anti-Herglotz at `z`, then the
trace carried only by free critical-line-reflection orbits is anti-Herglotz at `z`. -/
theorem xiOffCriticalRelativeResolventTrace_im_nonpos_of_lineConj_pairs
    (z : ℂ) (hXi : XiC z ≠ 0)
    (hpairsign : ∀ q : XiZeroCopy,
      (xiRelativeResolventTerm z q +
        xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)).im ≤ 0) :
    (xiOffCriticalRelativeResolventTrace z).im ≤ 0 := by
  let C : Set XiZeroCopy := xiCriticalLineZeroCopySet
  let residual : XiZeroCopy → ℂ :=
    (Cᶜ).indicator (xiRelativeResolventTerm z)
  have hsum : Summable (xiRelativeResolventTerm z) :=
    summable_xiRelativeResolventTerm hXi
  have hresidual : Summable residual := hsum.indicator _
  have hfixed (q : XiZeroCopy) (hq : q ∈ C) :
      xiZeroCopyLineConjEquiv q = q := by
    exact (mem_xiCriticalLineZeroCopySet_iff_lineConj_fixed q).mp
      (by simpa only [C] using hq)
  have hmem (q : XiZeroCopy) :
      xiZeroCopyLineConjEquiv q ∈ C ↔ q ∈ C := by
    constructor
    · intro hq
      have hfix := hfixed (xiZeroCopyLineConjEquiv q) hq
      have hinvol :=
        DeningerMeyerGaussianGreen.xiZeroCopyLineConjEquiv_apply_apply q
      have heq : xiZeroCopyLineConjEquiv q = q := by
        rw [hfix] at hinvol
        exact hinvol
      simpa only [heq] using hq
    · intro hq
      simpa only [hfixed q hq] using hq
  have hresidualJ : Summable
      (fun q : XiZeroCopy => residual (xiZeroCopyLineConjEquiv q)) :=
    (xiZeroCopyLineConjEquiv.summable_iff).mpr hresidual
  have hpair := hresidual.add hresidualJ
  have hreindex :
      (∑' q : XiZeroCopy, residual (xiZeroCopyLineConjEquiv q)) =
        ∑' q : XiZeroCopy, residual q :=
    xiZeroCopyLineConjEquiv.tsum_eq residual
  have hpairsum :
      (∑' q : XiZeroCopy,
          (residual q + residual (xiZeroCopyLineConjEquiv q))) =
        2 * ∑' q : XiZeroCopy, residual q := by
    rw [hresidual.tsum_add hresidualJ, hreindex]
    ring
  have hpairsumIm := congrArg Complex.im hpairsum
  rw [Complex.im_tsum hpair] at hpairsumIm
  norm_num [mul_im] at hpairsumIm
  have hpairsumIm' :
      (∑' q : XiZeroCopy,
          (residual q + residual (xiZeroCopyLineConjEquiv q)).im) =
        2 * (∑' q : XiZeroCopy, residual q).im := by
    simpa only [Complex.add_im] using hpairsumIm
  have hpairsign' :
      (∑' q : XiZeroCopy,
          (residual q + residual (xiZeroCopyLineConjEquiv q)).im) ≤ 0 := by
    refine tsum_nonpos fun q => ?_
    by_cases hq : q ∈ C
    · have hqJ : xiZeroCopyLineConjEquiv q ∈ C := (hmem q).2 hq
      simp [residual, hq, hqJ]
    · have hqJ : xiZeroCopyLineConjEquiv q ∉ C :=
        fun h => hq ((hmem q).1 h)
      simpa only [residual, Set.indicator, Set.mem_compl_iff,
        hq, hqJ, not_false_eq_true, ↓reduceIte] using hpairsign q
  have hoffEq :
      xiOffCriticalRelativeResolventTrace z =
        ∑' q : XiZeroCopy, residual q := by
    rw [xiOffCriticalRelativeResolventTrace]
    calc
      (∑' q : ↥(xiCriticalLineZeroCopySetᶜ),
          xiRelativeResolventTerm z q.1) =
          ∑' q : XiZeroCopy,
            (xiCriticalLineZeroCopySetᶜ).indicator
              (xiRelativeResolventTerm z) q :=
        tsum_subtype _ _
      _ = ∑' q : XiZeroCopy, residual q := by
        apply tsum_congr
        intro q
        simp only [residual, C]
  rw [hoffEq]
  linarith

/-- Deleting the whole critical fixed locus preserves verified-height accretivity. -/
theorem xiOffCriticalRelativeResolventTrace_im_nonpos_of_verifiedHeight
    (H R : ℝ) (hverified : RHVerifiedThrough H)
    (hband : R + 1 / 2 ≤ H)
    (z : ℂ) (hzIm : 0 < z.im) (hzRe : |z.re| ≤ R) :
    (xiOffCriticalRelativeResolventTrace z).im ≤ 0 := by
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_upperHalf_verifiedHeightBand
      H R hverified hband z hzIm hzRe
  exact xiOffCriticalRelativeResolventTrace_im_nonpos_of_lineConj_pairs
    z hXi fun q =>
      xiRelativeResolventTerm_lineConj_pair_im_nonpos_of_verifiedHeight
        H R hverified hband z hzIm hzRe q

/-- On a source-certified verified-height band, source dissipation pays the complete
multiplicity-exact critical-line Poisson trace. -/
theorem xiCriticalLinePoissonTrace_le_neg_im_continuedPrimeArchSource_of_verifiedHeight
    (H R : ℝ) (hverified : RHVerifiedThrough H)
    (hband : R + 1 / 2 ≤ H)
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ R) :
    xiCriticalLinePoissonTrace z ≤
      -(continuedPrimeArchSourceRelativeTrace z).im := by
  have hspos : 0 < (1 / 2 + z * I).re := centeredAbscissa_re_pos hzHalf
  have hs1 : 1 / 2 + z * I ≠ 1 := centeredAbscissa_ne_one hzIm
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_upperHalf_verifiedHeightBand
      H R hverified hband z hzIm hzRe
  have hzeta : riemannZeta (1 / 2 + z * I) ≠ 0 :=
    (xi_eq_zero_iff hspos hs1).not.mp (by simpa only [XiC] using hXi)
  have hconservation :=
    neg_im_continuedPrimeArchSource_sub_criticalLinePoissonTrace_eq_neg_im_offCritical
      z hzIm hzHalf hzeta
  have hfree :=
    xiOffCriticalRelativeResolventTrace_im_nonpos_of_verifiedHeight
      H R hverified hband z hzIm hzRe
  linarith

/-- Complete critical-locus Poisson reserve through the source-certified radius `233 / 20`. -/
theorem xiCriticalLinePoissonTrace_le_neg_im_continuedPrimeArchSource_twoHundredThirtyThree_twentieths
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ 233 / 20) :
    xiCriticalLinePoissonTrace z ≤
      -(continuedPrimeArchSourceRelativeTrace z).im :=
  xiCriticalLinePoissonTrace_le_neg_im_continuedPrimeArchSource_of_verifiedHeight
    (243 / 20) (233 / 20) rhVerifiedThrough_twoHundredFortyThree_twentieths
    (by norm_num) z hzIm hzHalf hzRe

/-- Remaining complete critical-locus Poisson-margin obligation above a positive frequency. -/
def CriticalLocusPrimeGammaPoissonMarginAbove (R : ℝ) : Prop :=
  ∀ z : ℂ, R < z.re → 0 < z.im → z.im < 1 / 2 →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
      xiCriticalLinePoissonTrace z ≤
        -(continuedPrimeArchSourceRelativeTrace z).im

/-- A verified-height prefix reduces the complete critical-locus margin exactly to its positive
frequency tail. -/
theorem riemannHypothesis_iff_criticalLocusPrimeGammaPoissonMarginAbove_of_verifiedHeight
    (H R : ℝ) (hverified : RHVerifiedThrough H)
    (hband : R + 1 / 2 ≤ H) :
    RiemannHypothesis ↔ CriticalLocusPrimeGammaPoissonMarginAbove R := by
  constructor
  · intro hRH z _hzRe hzIm hzHalf hzeta
    exact le_of_eq
      (xiCriticalLinePoissonTrace_eq_neg_im_continuedPrimeArchSource_of_riemannHypothesis
        hRH z hzIm hzHalf hzeta)
  · intro hmargin
    apply (continuedPrimeArchPositiveFrequencyAbove_iff_rh_of_verifiedHeight
      H R hverified hband).mp
    intro z hzIm hzHalf hzRe hzeta
    have hpay := hmargin z hzRe hzIm hzHalf hzeta
    have hnonneg := xiCriticalLinePoissonTrace_nonneg z hzIm.le
    linarith

/-- Exact sharpened endpoint: after source-certified fourth-trace exclusion, only the complete
critical-locus Poisson margin above `233 / 20` remains RH-bearing. -/
theorem riemannHypothesis_iff_criticalLocusPrimeGammaPoissonMarginAbove_twoHundredThirtyThree_twentieths :
    RiemannHypothesis ↔
      CriticalLocusPrimeGammaPoissonMarginAbove (233 / 20) :=
  riemannHypothesis_iff_criticalLocusPrimeGammaPoissonMarginAbove_of_verifiedHeight
    (243 / 20) (233 / 20) rhVerifiedThrough_twoHundredFortyThree_twentieths
    (by norm_num)

/-- Remaining passivity obligation for only the free reflection-orbit sector above a positive
frequency. -/
def OffCriticalRelativeResolventPositiveFrequencyAbove (R : ℝ) : Prop :=
  ∀ z : ℂ, R < z.re → 0 < z.im → z.im < 1 / 2 →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
      (xiOffCriticalRelativeResolventTrace z).im ≤ 0

/-- Exact pointwise cancellation identifies the complete critical-locus source margin with
passivity of the free reflection-orbit sector alone. -/
theorem criticalLocusPrimeGammaPoissonMarginAbove_iff_offCriticalRelativeResolventPositiveFrequencyAbove
    (R : ℝ) :
    CriticalLocusPrimeGammaPoissonMarginAbove R ↔
      OffCriticalRelativeResolventPositiveFrequencyAbove R := by
  constructor
  · intro hmargin z hzRe hzIm hzHalf hzeta
    have hpay := hmargin z hzRe hzIm hzHalf hzeta
    have hconservation :=
      neg_im_continuedPrimeArchSource_sub_criticalLinePoissonTrace_eq_neg_im_offCritical
        z hzIm hzHalf hzeta
    linarith
  · intro hfree z hzRe hzIm hzHalf hzeta
    have hsign := hfree z hzRe hzIm hzHalf hzeta
    have hconservation :=
      neg_im_continuedPrimeArchSource_sub_criticalLinePoissonTrace_eq_neg_im_offCritical
        z hzIm hzHalf hzeta
    linarith

/-- Final source-certified free-sector endpoint: RH is equivalent to passivity of only the free
reflection-orbit trace, only at positive frequencies above `233 / 20`. -/
theorem riemannHypothesis_iff_offCriticalRelativeResolventPositiveFrequencyAbove_twoHundredThirtyThree_twentieths :
    RiemannHypothesis ↔
      OffCriticalRelativeResolventPositiveFrequencyAbove (233 / 20) := by
  rw [←
    criticalLocusPrimeGammaPoissonMarginAbove_iff_offCriticalRelativeResolventPositiveFrequencyAbove]
  exact
    riemannHypothesis_iff_criticalLocusPrimeGammaPoissonMarginAbove_twoHundredThirtyThree_twentieths

end

end RHTower
