import GaloisForLFunctions.RHTower.PrimeArchExactOffLineQuartetAccretivity
import GaloisForLFunctions.RHTower.XiWeilHardyFiberDeflatedCentralBand

/-!
# Hardy-fiber deletion across the exact off-line-quartet band

The fourfold FE--Schwarz orbit budget is used only to force every off-line Xi atom far from an
admissible central band.  The resulting resolvent sign is still proved by critical-line-conjugate
pairs.  A complete critical fiber is pointwise fixed by that pairing involution, so deleting it
preserves the exact quartet-band argument.

Consequently the continued prime--Gamma source pays the full multiplicity-weighted Poisson kernel
of any fixed critical Xi fiber throughout every exact quartet-admissible band.  At the concrete
radius `218 / 25`, this strengthens the earlier radius-four Hardy-fiber reserve and moves the
remaining one-fiber quantitative RH obligation entirely above `218 / 25`.
-/

open Complex Set
open scoped BigOperators

namespace RHTower

noncomputable section

set_option maxHeartbeats 800000 in
/-- Deleting one complete critical fiber preserves the exact off-line-quartet central-band sign. -/
theorem xiRelativeResolventTrace_sub_criticalFiber_im_nonpos_exactOffLineQuartetBand
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2)
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (z : ℂ) (hzIm : 0 < z.im) (hzRe : |z.re| ≤ R) :
    (xiRelativeResolventTrace z -
      ∑ q ∈ xiZeroCopyFiber ρ, xiRelativeResolventTerm z q).im ≤ 0 := by
  let S : Finset XiZeroCopy := xiZeroCopyFiber ρ
  let residual : XiZeroCopy → ℂ :=
    ((↑S : Set XiZeroCopy)ᶜ).indicator (xiRelativeResolventTerm z)
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_upperHalf_exactOffLineQuartetBand R hband z hzIm hzRe
  have hsum : Summable (xiRelativeResolventTerm z) :=
    summable_xiRelativeResolventTerm hXi
  have hresidual : Summable residual := hsum.indicator _
  have hfixed (q : XiZeroCopy) (hq : q ∈ S) :
      xiZeroCopyLineConjEquiv q = q := by
    apply (xiZeroCopyLineConjEquiv_eq_self_iff_re_eq_half q).2
    have hqρ : q.1 = ρ :=
      mem_xiZeroCopyFiber.mp (by simpa only [S] using hq)
    rw [hqρ]
    exact hρ
  have hmem (q : XiZeroCopy) :
      xiZeroCopyLineConjEquiv q ∈ S ↔ q ∈ S := by
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
  have hpairsign :
      (∑' q : XiZeroCopy,
          (residual q + residual (xiZeroCopyLineConjEquiv q)).im) ≤ 0 := by
    refine tsum_nonpos fun q => ?_
    by_cases hq : q ∈ S
    · have hqJ : xiZeroCopyLineConjEquiv q ∈ S := (hmem q).2 hq
      simp [residual, hq, hqJ]
    · have hqJ : xiZeroCopyLineConjEquiv q ∉ S :=
        fun h => hq ((hmem q).1 h)
      simpa only [residual, Set.indicator, Set.mem_compl_iff, Finset.mem_coe,
        hq, hqJ, not_false_eq_true, ↓reduceIte] using
        xiRelativeResolventTerm_lineConj_pair_im_nonpos_offLineOrbit
          R hband z hzIm hzRe q
  have htraceResidual :
      xiRelativeResolventTrace z -
          ∑ q ∈ xiZeroCopyFiber ρ, xiRelativeResolventTerm z q =
        ∑' q : XiZeroCopy, residual q := by
    have hsplit := hsum.sum_add_tsum_subtype_compl (xiZeroCopyFiber ρ)
    have hsub :
        xiRelativeResolventTrace z -
            ∑ q ∈ xiZeroCopyFiber ρ, xiRelativeResolventTerm z q =
          ∑' q : {q : XiZeroCopy // q ∉ xiZeroCopyFiber ρ},
            xiRelativeResolventTerm z q := by
      rw [xiRelativeResolventTrace, ← hsplit]
      ring
    rw [hsub]
    calc
      (∑' q : {q : XiZeroCopy // q ∉ xiZeroCopyFiber ρ},
          xiRelativeResolventTerm z q) =
          ∑' q : XiZeroCopy,
            ({q : XiZeroCopy | q ∉ xiZeroCopyFiber ρ}).indicator
              (xiRelativeResolventTerm z) q :=
        tsum_subtype _ _
      _ = ∑' q : XiZeroCopy, residual q := by
        apply tsum_congr
        intro q
        by_cases hq : q ∈ xiZeroCopyFiber ρ
        · have hqeq : q.1 = ρ := mem_xiZeroCopyFiber.mp hq
          simp [residual, S, Set.indicator, hq, hqeq]
        · have hqne : q.1 ≠ ρ :=
            fun heq => hq (mem_xiZeroCopyFiber.mpr heq)
          simp [residual, S, Set.indicator, hq, hqne]
  rw [htraceResidual]
  linarith

/-- The fixed-critical-fiber-deflated continued source is passive on every exact quartet band. -/
theorem ccmFixedCriticalFiberDeflatedRelativeTrace_im_nonpos_exactOffLineQuartetBand
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2)
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ R) :
    (ccmFixedFiberDeflatedRelativeTrace ρ z).im ≤ 0 := by
  have hspos : 0 < (1 / 2 + z * I).re := centeredAbscissa_re_pos hzHalf
  have hs1 : 1 / 2 + z * I ≠ 1 := centeredAbscissa_ne_one hzIm
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_upperHalf_exactOffLineQuartetBand R hband z hzIm hzRe
  have hzeta : riemannZeta (1 / 2 + z * I) ≠ 0 :=
    (xi_eq_zero_iff hspos hs1).not.mp (by simpa only [XiC] using hXi)
  rw [ccmFixedFiberDeflatedRelativeTrace_eq_xiTrace_sub_fiber
    ρ hspos hs1 hzeta]
  exact xiRelativeResolventTrace_sub_criticalFiber_im_nonpos_exactOffLineQuartetBand
    ρ hρ R hband z hzIm hzRe

/-- Exact quartet-band dissipation pays the full Poisson mass of every critical Xi fiber. -/
theorem fixedCriticalFiber_primeGammaPoissonMargin_exactOffLineQuartetBand
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2)
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ R) :
    ((xiZeroCopyFiber ρ).card : ℝ) * z.im /
        Complex.normSq (xiSpectralPointSupport ρ - z) ≤
      -(continuedPrimeArchSourceRelativeTrace z).im := by
  have hαim : (xiSpectralPointSupport ρ).im = 0 :=
    (xiSpectralPointSupport_im_eq_zero_iff ρ).2 hρ
  have hdeflated :=
    ccmFixedCriticalFiberDeflatedRelativeTrace_im_nonpos_exactOffLineQuartetBand
      ρ hρ R hband z hzIm hzHalf hzRe
  rw [ccmFixedFiberDeflatedRelativeTrace_im_eq_add_poisson ρ z hαim]
    at hdeflated
  linarith

/-- Hardy's critical fiber makes the source sign strictly negative on every exact quartet band. -/
theorem continuedPrimeArchSourceRelativeTrace_im_neg_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ R) :
    (continuedPrimeArchSourceRelativeTrace z).im < 0 := by
  obtain ⟨ρ, hρ⟩ := exists_criticalLine_xiDivisorSupport_of_hardy
  have hmargin :=
    fixedCriticalFiber_primeGammaPoissonMargin_exactOffLineQuartetBand
      ρ hρ R hband z hzIm hzHalf hzRe
  have hcardNat : 0 < (xiZeroCopyFiber ρ).card := by
    rw [Finset.card_pos]
    exact ⟨xiFirstZeroCopy ρ, mem_xiZeroCopyFiber.mpr rfl⟩
  have hcard : 0 < ((xiZeroCopyFiber ρ).card : ℝ) := by
    exact_mod_cast hcardNat
  have hαim : (xiSpectralPointSupport ρ).im = 0 :=
    (xiSpectralPointSupport_im_eq_zero_iff ρ).2 hρ
  have hne : xiSpectralPointSupport ρ - z ≠ 0 := by
    rw [sub_ne_zero]
    intro heq
    have him := congrArg Complex.im heq
    rw [hαim] at him
    linarith
  have hnorm : 0 < Complex.normSq (xiSpectralPointSupport ρ - z) :=
    Complex.normSq_pos.mpr hne
  have hfloor : 0 < ((xiZeroCopyFiber ρ).card : ℝ) * z.im /
      Complex.normSq (xiSpectralPointSupport ρ - z) :=
    div_pos (mul_pos hcard hzIm) hnorm
  linarith

/-- Concrete unconditional Hardy-fiber Poisson reserve through radius `218 / 25`. -/
theorem fixedCriticalFiber_primeGammaPoissonMargin_twoHundredEighteen_twentyFifths
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2)
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ 218 / 25) :
    ((xiZeroCopyFiber ρ).card : ℝ) * z.im /
        Complex.normSq (xiSpectralPointSupport ρ - z) ≤
      -(continuedPrimeArchSourceRelativeTrace z).im :=
  fixedCriticalFiber_primeGammaPoissonMargin_exactOffLineQuartetBand
    ρ hρ (218 / 25)
      xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths
    z hzIm hzHalf hzRe

/-- Remaining one-fiber quantitative source obligation above an arbitrary positive frequency. -/
def FixedFiberPrimeGammaPoissonMarginAbove
    (ρ : XiDivisorSupport) (R : ℝ) : Prop :=
  ∀ z : ℂ, R < z.re → 0 < z.im → z.im < 1 / 2 →
    riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
      ((xiZeroCopyFiber ρ).card : ℝ) * z.im /
          Complex.normSq (xiSpectralPointSupport ρ - z) ≤
        -(continuedPrimeArchSourceRelativeTrace z).im

/-- A positive-frequency one-fiber margin implies the ordinary source sign above the same edge. -/
theorem continuedPrimeArchPositiveFrequencyAbove_of_fixedFiberPoissonMarginAbove
    (ρ : XiDivisorSupport) (R : ℝ)
    (hmargin : FixedFiberPrimeGammaPoissonMarginAbove ρ R) :
    ContinuedPrimeArchPositiveFrequencyAbove R := by
  intro z hzIm hzHalf hzRe hzeta
  have hz := hmargin z hzRe hzIm hzHalf hzeta
  have hfloor : 0 ≤ ((xiZeroCopyFiber ρ).card : ℝ) * z.im /
      Complex.normSq (xiSpectralPointSupport ρ - z) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hzIm.le)
      (Complex.normSq_nonneg _)
  linarith

/-- On every exact quartet-admissible band, RH is equivalent to one fixed critical fiber's
Poisson margin only above the positive band edge. -/
theorem riemannHypothesis_iff_fixedCriticalFiberPrimeGammaPoissonMarginAbove
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2)
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R) :
    RiemannHypothesis ↔ FixedFiberPrimeGammaPoissonMarginAbove ρ R := by
  constructor
  · intro hRH z _hzRe hzIm hzHalf hzeta
    exact (riemannHypothesis_iff_fixedCriticalFiberPrimeGammaPoissonMargin ρ hρ).mp
      hRH z hzIm hzHalf hzeta
  · intro hmargin
    exact (continuedPrimeArchPositiveFrequencyAbove_iff_rh_of_exactOffLineQuartetBand
      R hband).mp
        (continuedPrimeArchPositiveFrequencyAbove_of_fixedFiberPoissonMarginAbove
          ρ R hmargin)

/-- Sharp concrete reduction: only the fixed-fiber Poisson margin above `218 / 25` remains. -/
theorem riemannHypothesis_iff_fixedCriticalFiberPrimeGammaPoissonMarginAbove_twoHundredEighteen_twentyFifths
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2) :
    RiemannHypothesis ↔
      FixedFiberPrimeGammaPoissonMarginAbove ρ (218 / 25) :=
  riemannHypothesis_iff_fixedCriticalFiberPrimeGammaPoissonMarginAbove
    ρ hρ (218 / 25)
      xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths

/-- Hardy supplies an unconditional fiber for the one-sided `218 / 25` Poisson-margin criterion. -/
theorem exists_hardyCriticalFiber_primeGammaPoissonMarginAbove_twoHundredEighteen_twentyFifths_criterion :
    ∃ ρ : XiDivisorSupport,
      (ρ : ℂ).re = 1 / 2 ∧
        (RiemannHypothesis ↔
          FixedFiberPrimeGammaPoissonMarginAbove ρ (218 / 25)) := by
  obtain ⟨ρ, hρ⟩ := exists_criticalLine_xiDivisorSupport_of_hardy
  exact ⟨ρ, hρ,
    riemannHypothesis_iff_fixedCriticalFiberPrimeGammaPoissonMarginAbove_twoHundredEighteen_twentyFifths
      ρ hρ⟩

end

end RHTower
