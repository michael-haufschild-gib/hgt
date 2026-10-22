import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerGaussianLineWronskianGreenComparison
import GaloisForLFunctions.RHTower.PrimeArchHighFrequencyAccretivity
import GaloisForLFunctions.RHTower.XiWeilHardyFiberDeflatedAntiHerglotz
import GaloisForLFunctions.RHTower.XiWeilSameFiberAtomIsotropy

/-!
# Unconditional central-band passivity after deleting a Hardy fiber

The unconditional central-frequency proof pairs every Xi resolvent atom with its critical-line
reflection.  A complete fiber on the critical line is pointwise fixed by that reflection.  Deleting
such a fiber therefore preserves the pairing involution on the complement, and every remaining
pair keeps the endpoint-height-gap anti-Herglotz sign.

This yields an unconditional strengthening of central-band source passivity: the negative
imaginary part of the continued prime--Gamma trace pays the exact positive Poisson mass of any
fixed critical Xi fiber.  Hardy's theorem supplies such a fiber, so the formerly non-strict central
sign is in fact uniformly pointwise strict, with an explicit arithmetic lower margin.
-/

open Complex Set
open scoped BigOperators

namespace RHTower

noncomputable section

set_option maxHeartbeats 800000 in
/-- Deleting a complete critical fiber preserves the unconditional anti-Herglotz sign on every
central frequency band of radius at most four. -/
theorem xiRelativeResolventTrace_sub_criticalFiber_im_nonpos_lowFrequency
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2)
    (R : ℝ) (hR : 0 ≤ R) (hRfour : R ≤ 4)
    (z : ℂ) (hzIm : 0 < z.im) (hzRe : |z.re| ≤ R) :
    (xiRelativeResolventTrace z -
      ∑ q ∈ xiZeroCopyFiber ρ, xiRelativeResolventTerm z q).im ≤ 0 := by
  let S : Finset XiZeroCopy := xiZeroCopyFiber ρ
  let residual : XiZeroCopy → ℂ :=
    ((↑S : Set XiZeroCopy)ᶜ).indicator (xiRelativeResolventTerm z)
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_abs_re_le_four (hzRe.trans hRfour)
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
        xiRelativeResolventTerm_lineConj_pair_im_nonpos
          R hR hRfour z hzIm hzRe q
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

/-- The fixed-critical-fiber-deflated continued source is unconditionally passive on the same
central band. -/
theorem ccmFixedCriticalFiberDeflatedRelativeTrace_im_nonpos_lowFrequency
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2)
    (R : ℝ) (hR : 0 ≤ R) (hRfour : R ≤ 4)
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ R) :
    (ccmFixedFiberDeflatedRelativeTrace ρ z).im ≤ 0 := by
  have hspos : 0 < (1 / 2 + z * I).re := centeredAbscissa_re_pos hzHalf
  have hs1 : 1 / 2 + z * I ≠ 1 := centeredAbscissa_ne_one hzIm
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_abs_re_le_four (hzRe.trans hRfour)
  have hzeta : riemannZeta (1 / 2 + z * I) ≠ 0 :=
    (xi_eq_zero_iff hspos hs1).not.mp (by simpa only [XiC] using hXi)
  rw [ccmFixedFiberDeflatedRelativeTrace_eq_xiTrace_sub_fiber
    ρ hspos hs1 hzeta]
  exact xiRelativeResolventTrace_sub_criticalFiber_im_nonpos_lowFrequency
    ρ hρ R hR hRfour z hzIm hzRe

/-- Unconditional central-band source dissipation pays the exact Poisson mass of every fixed
critical Xi fiber. -/
theorem fixedCriticalFiber_primeGammaPoissonMargin_lowFrequency
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2)
    (R : ℝ) (hR : 0 ≤ R) (hRfour : R ≤ 4)
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ R) :
    ((xiZeroCopyFiber ρ).card : ℝ) * z.im /
        Complex.normSq (xiSpectralPointSupport ρ - z) ≤
      -(continuedPrimeArchSourceRelativeTrace z).im := by
  have hαim : (xiSpectralPointSupport ρ).im = 0 :=
    (xiSpectralPointSupport_im_eq_zero_iff ρ).2 hρ
  have hdeflated :=
    ccmFixedCriticalFiberDeflatedRelativeTrace_im_nonpos_lowFrequency
      ρ hρ R hR hRfour z hzIm hzHalf hzRe
  rw [ccmFixedFiberDeflatedRelativeTrace_im_eq_add_poisson ρ z hαim]
    at hdeflated
  linarith

/-- Hardy's critical fiber makes the unconditional central-band source sign strictly negative. -/
theorem continuedPrimeArchSourceRelativeTrace_im_neg_lowFrequency
    (R : ℝ) (hR : 0 ≤ R) (hRfour : R ≤ 4)
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ R) :
    (continuedPrimeArchSourceRelativeTrace z).im < 0 := by
  obtain ⟨ρ, hρ⟩ := exists_criticalLine_xiDivisorSupport_of_hardy
  have hmargin := fixedCriticalFiber_primeGammaPoissonMargin_lowFrequency
    ρ hρ R hR hRfour z hzIm hzHalf hzRe
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

/-- Full radius-four specialization of the unconditional fixed-fiber Poisson margin. -/
theorem fixedCriticalFiber_primeGammaPoissonMargin_four
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2)
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ 4) :
    ((xiZeroCopyFiber ρ).card : ℝ) * z.im /
        Complex.normSq (xiSpectralPointSupport ρ - z) ≤
      -(continuedPrimeArchSourceRelativeTrace z).im :=
  fixedCriticalFiber_primeGammaPoissonMargin_lowFrequency
    ρ hρ 4 (by norm_num) (by norm_num) z hzIm hzHalf hzRe

end

end RHTower
