import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap
import GaloisForLFunctions.RHTower.PrimeArchAntiHerglotzGate
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion
import GaloisForLFunctions.RHTower.XiEndpointSourceHeightGap
import GaloisForLFunctions.RHTower.XiWeilOneCauchyGate
import GaloisForLFunctions.RHTower.XiGuinandWeilSymmetricContour
import GaloisForLFunctions.RHTower.CCM.CCMCompletedPrimeGammaAccretivityCriterion

/-!
# Prime--archimedean high-frequency accretivity

The strong endpoint source bound places every centered Xi zero outside squared height `41 / 2`.
Pairing
each relative-resolvent atom with its critical-line conjugate then proves the upper-half-plane sign
unconditionally on a nontrivial central frequency band.  The involution `z ↦ -conj z` removes the
negative-frequency half of the remaining condition.  Finally, Gaussian-rational density and
continuity reduce the open source obligation to a countable family of high positive-frequency
prime--Gamma values.

The capstone is an exact criterion, but its content is a hypothesis discharge: the compact central
band, all negative frequencies, and all irrational test points no longer belong to the open RH
input.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

set_option maxRecDepth 10000 in
/-- Exact imaginary part of a relative-resolvent atom paired with its complex conjugate. -/
lemma relativeResolvent_conj_pair_im_formula
    (z a : ℂ) (ha : a ≠ 0) (hza : z ≠ a)
    (hzac : z ≠ (starRingEnd ℂ) a) :
    ((a⁻¹ - (a - z)⁻¹) +
        (((starRingEnd ℂ) a)⁻¹ - ((starRingEnd ℂ) a - z)⁻¹)).im =
      -2 * z.im *
          ((z.re - a.re) ^ (2 : ℕ) + z.im ^ (2 : ℕ) - a.im ^ (2 : ℕ)) /
        (((z.re - a.re) ^ (2 : ℕ) + (z.im - a.im) ^ (2 : ℕ)) *
          ((z.re - a.re) ^ (2 : ℕ) + (z.im + a.im) ^ (2 : ℕ))) := by
  have hca : (starRingEnd ℂ) a ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 ha
  have haz : a - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hza)
  have hcaz : (starRingEnd ℂ) a - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzac)
  simp only [add_im, sub_im]
  rw [Complex.inv_im, Complex.inv_im, Complex.inv_im, Complex.inv_im]
  simp only [Complex.conj_re, Complex.conj_im, neg_neg, sub_im,
    Complex.normSq_apply, sub_re]
  have hna : a.re ^ (2 : ℕ) + a.im ^ (2 : ℕ) ≠ 0 := by
    simpa only [Complex.normSq_apply, pow_two] using
      (Complex.normSq_pos.mpr ha).ne'
  have hnaz :
      (a.re - z.re) ^ (2 : ℕ) + (a.im - z.im) ^ (2 : ℕ) ≠ 0 := by
    simpa only [Complex.normSq_apply, sub_re, sub_im, pow_two] using
      (Complex.normSq_pos.mpr haz).ne'
  have hncaz :
      (a.re - z.re) ^ (2 : ℕ) + (-a.im - z.im) ^ (2 : ℕ) ≠ 0 := by
    simpa only [Complex.normSq_apply, Complex.conj_re, Complex.conj_im,
      sub_re, sub_im, pow_two] using (Complex.normSq_pos.mpr hcaz).ne'
  have hdnaz :
      (z.re - a.re) ^ (2 : ℕ) + (z.im - a.im) ^ (2 : ℕ) ≠ 0 := by
    have h : z - a ≠ 0 := sub_ne_zero.mpr hza
    simpa only [Complex.normSq_apply, sub_re, sub_im, pow_two] using
      (Complex.normSq_pos.mpr h).ne'
  have hdncaz :
      (z.re - a.re) ^ (2 : ℕ) + (z.im + a.im) ^ (2 : ℕ) ≠ 0 := by
    have h : z - (starRingEnd ℂ) a ≠ 0 := sub_ne_zero.mpr hzac
    simpa only [Complex.normSq_apply, Complex.conj_re, Complex.conj_im,
      sub_re, sub_im, sub_neg_eq_add, pow_two] using
      (Complex.normSq_pos.mpr h).ne'
  field_simp [hna, hnaz, hncaz, hdnaz, hdncaz]
  ring

/-- **The anti-Herglotz sign of a line-conjugate resolvent pair, from the separation core.**
Writing `a` for the spectral point of `q`, the pair's imaginary part is
`−2·z.im·((z.re − a.re)² + z.im² − a.im²)` over a positive denominator, so in the upper half-plane
a positive core `0 < (z.re − a.re)² + z.im² − a.im²` already forces the sign.  The core also
separates `z` from `a` and from its line conjugate — both would make it vanish — which is what
keeps the two resolvent terms finite.  Every accretive-band hypothesis in the tower enters only
through this one inequality. -/
lemma xiRelativeResolventTerm_lineConj_pair_im_nonpos_of_core
    (z : ℂ) (hzIm : 0 < z.im) (q : XiZeroCopy)
    (hcore : 0 < (z.re - (xiSpectralPoint q).re) ^ (2 : ℕ) + z.im ^ (2 : ℕ)
      - (xiSpectralPoint q).im ^ (2 : ℕ)) :
    (xiRelativeResolventTerm z q +
      xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)).im ≤ 0 := by
  set a : ℂ := xiSpectralPoint q with ha_def
  have hza : z ≠ a := by
    intro h
    rw [h] at hcore
    nlinarith [hcore]
  have hzac : z ≠ (starRingEnd ℂ) a := by
    intro h
    rw [h] at hcore
    simp only [Complex.conj_re, Complex.conj_im] at hcore
    nlinarith [hcore]
  have hdenOne : 0 < (z.re - a.re) ^ (2 : ℕ) + (z.im - a.im) ^ (2 : ℕ) := by
    have hne : z - a ≠ 0 := sub_ne_zero.mpr hza
    have hnorm : 0 < Complex.normSq (z - a) := Complex.normSq_pos.mpr hne
    simpa [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, sq] using hnorm
  have hdenTwo : 0 < (z.re - a.re) ^ (2 : ℕ) + (z.im + a.im) ^ (2 : ℕ) := by
    have hne : z - (starRingEnd ℂ) a ≠ 0 := sub_ne_zero.mpr hzac
    have hnorm : 0 < Complex.normSq (z - (starRingEnd ℂ) a) := Complex.normSq_pos.mpr hne
    simpa [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re,
      Complex.conj_im, sq, sub_neg_eq_add] using hnorm
  rw [xiRelativeResolventTerm, xiRelativeResolventTerm,
    xiSpectralPoint_lineConj]
  change ((a⁻¹ - (a - z)⁻¹) +
      (((starRingEnd ℂ) a)⁻¹ - ((starRingEnd ℂ) a - z)⁻¹)).im ≤ 0
  rw [relativeResolvent_conj_pair_im_formula z a
    (xiSpectralPoint_ne_zero q) hza (by simpa using hzac)]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by nlinarith [hzIm]) hcore.le)
    (mul_nonneg hdenOne.le hdenTwo.le)

/-- The endpoint height gap makes every conjugate-paired Xi resolvent atom nonpositive throughout
a central frequency band. -/
lemma xiRelativeResolventTerm_lineConj_pair_im_nonpos
    (R : ℝ) (hR : 0 ≤ R) (hRfour : R ≤ 4)
    (z : ℂ) (hzIm : 0 < z.im) (hzRe : |z.re| ≤ R)
    (q : XiZeroCopy) :
    (xiRelativeResolventTerm z q +
      xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)).im ≤ 0 := by
  let a : ℂ := xiSpectralPoint q
  have hareSq : (41 / 2 : ℝ) < a.re ^ (2 : ℕ) := by
    simpa [a, xiSpectralPoint, mul_re] using
      xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have hareAbs : R + 1 / 2 < |a.re| := by
    nlinarith [sq_abs a.re, abs_nonneg a.re]
  have haimMem := xiSpectralPoint_im_mem_openHalf q
  have haimAbs : |a.im| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith [haimMem.1, haimMem.2]
  have hdistLower : |a.re| - |z.re| ≤ |a.re - z.re| :=
    abs_sub_abs_le_abs_sub a.re z.re
  have hdistAbs : 1 / 2 < |z.re - a.re| := by
    rw [abs_sub_comm]
    linarith
  have hdistSq : a.im ^ (2 : ℕ) < (z.re - a.re) ^ (2 : ℕ) := by
    nlinarith [sq_abs a.im, sq_abs (z.re - a.re),
      abs_nonneg a.im, abs_nonneg (z.re - a.re)]
  have hcore : 0 < (z.re - a.re) ^ (2 : ℕ) + z.im ^ (2 : ℕ) - a.im ^ (2 : ℕ) := by
    nlinarith [sq_nonneg z.im]
  exact xiRelativeResolventTerm_lineConj_pair_im_nonpos_of_core z hzIm q hcore

/-- Unconditional anti-Herglotz sign for the full Xi relative-resolvent trace on every central band
of radius at most four. -/
theorem xiRelativeResolventTrace_im_nonpos_lowFrequency
    (R : ℝ) (hR : 0 ≤ R) (hRfour : R ≤ 4)
    (z : ℂ) (hzIm : 0 < z.im) (hzRe : |z.re| ≤ R) :
    (xiRelativeResolventTrace z).im ≤ 0 := by
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_abs_re_le_four (hzRe.trans hRfour)
  have himsum :
      (∑' q : XiZeroCopy,
        (xiRelativeResolventTerm z q +
          xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)).im) ≤ 0 :=
    tsum_nonpos fun q =>
      xiRelativeResolventTerm_lineConj_pair_im_nonpos
        R hR hRfour z hzIm hzRe q
  linarith [tsum_lineConj_pair_im_eq_two_mul_xiRelativeResolventTrace_im hXi]

/-- Source-side form of the unconditional central-band sign. -/
theorem continuedPrimeArchSourceRelativeTrace_im_nonpos_lowFrequency
    (R : ℝ) (hR : 0 ≤ R) (hRfour : R ≤ 4)
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ R) :
    (continuedPrimeArchSourceRelativeTrace z).im ≤ 0 := by
  have hspos : 0 < (1 / 2 + z * I).re :=
    centeredAbscissa_re_pos (by linarith)
  have hs1 : 1 / 2 + z * I ≠ 1 :=
    centeredAbscissa_ne_one (by linarith)
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_abs_re_le_four (hzRe.trans hRfour)
  have hzeta : riemannZeta (1 / 2 + z * I) ≠ 0 := by
    exact (xi_eq_zero_iff hspos hs1).not.mp (by simpa only [XiC] using hXi)
  rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    hspos hs1 hzeta]
  exact xiRelativeResolventTrace_im_nonpos_lowFrequency
    R hR hRfour z hzIm hzRe

/-- A rational central band convenient for the one-sided RH criterion. -/
theorem continuedPrimeArchSourceRelativeTrace_im_nonpos_nine_tenths
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ 9 / 10) :
    (continuedPrimeArchSourceRelativeTrace z).im ≤ 0 := by
  exact continuedPrimeArchSourceRelativeTrace_im_nonpos_lowFrequency
    (9 / 10) (by norm_num) (by norm_num) z hzIm hzHalf hzRe

/-- The full rational central band supplied by the strong endpoint-source height gap. -/
theorem continuedPrimeArchSourceRelativeTrace_im_nonpos_four
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzRe : |z.re| ≤ 4) :
    (continuedPrimeArchSourceRelativeTrace z).im ≤ 0 := by
  exact continuedPrimeArchSourceRelativeTrace_im_nonpos_lowFrequency
    4 (by norm_num) (by norm_num) z hzIm hzHalf hzRe

/-- The upper-strip involution `z ↦ -conj z` flips frequency while preserving the
imaginary part of the continued source trace. -/
theorem continuedPrimeArchSourceRelativeTrace_neg_conj_im
    (z : ℂ) (hzIm : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    riemannZeta (1 / 2 + (-(starRingEnd ℂ) z) * I) ≠ 0 ∧
      (continuedPrimeArchSourceRelativeTrace (-(starRingEnd ℂ) z)).im =
        (continuedPrimeArchSourceRelativeTrace z).im := by
  let w : ℂ := -(starRingEnd ℂ) z
  have hspos : 0 < (1 / 2 + z * I).re :=
    centeredAbscissa_re_pos (by linarith)
  have hs1 : 1 / 2 + z * I ≠ 1 :=
    centeredAbscissa_ne_one (by linarith)
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain hspos hs1 hzeta
  have hcXi : XiC ((starRingEnd ℂ) z) ≠ 0 := XiC_ne_zero_conj hXi
  have hwXi : XiC w ≠ 0 := by
    dsimp only [w]
    rw [XiC_even]
    exact hcXi
  have hwIm : w.im = z.im := by simp [w]
  have hwpos : 0 < (1 / 2 + w * I).re := by
    simp [mul_re, hwIm]
    linarith
  have hw1 : 1 / 2 + w * I ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [mul_re, hwIm] at hre
    linarith
  have hwzeta : riemannZeta (1 / 2 + w * I) ≠ 0 := by
    exact (xi_eq_zero_iff hwpos hw1).not.mp (by simpa only [XiC] using hwXi)
  have hsourceZ :
      continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z := by
    rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hspos hs1 hzeta, ← logDeriv_XiC_eq_relativeResolventTrace hXi]
  have hsourceW :
      continuedPrimeArchSourceRelativeTrace w = logDeriv XiC w := by
    rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hwpos hw1 hwzeta, ← logDeriv_XiC_eq_relativeResolventTrace hwXi]
  have hlogConj :
      logDeriv XiC ((starRingEnd ℂ) z) =
        (starRingEnd ℂ) (logDeriv XiC z) := by
    rw [logDeriv_XiC_eq_relativeResolventTrace hcXi,
      logDeriv_XiC_eq_relativeResolventTrace hXi,
      xiRelativeResolventTrace_conj]
  refine ⟨by simpa only [w] using hwzeta, ?_⟩
  rw [show -(starRingEnd ℂ) z = w by rfl, hsourceW, hsourceZ]
  rw [show w = -(starRingEnd ℂ) z by rfl,
    logDeriv_XiC_neg, hlogConj]
  simp

/-- The only source sign still needed after the unconditional low-frequency theorem:
positive frequencies strictly above four. -/
def ContinuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz : Prop :=
  ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 → 4 < z.re →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
      (continuedPrimeArchSourceRelativeTrace z).im ≤ 0

/-- The one-sided high-frequency sign and the unconditional central-band theorem recover the
full anti-Herglotz source condition. -/
theorem continuedPrimeArchUpperAntiHerglotz_of_positiveHighFrequency
    (hhigh : ContinuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz) :
    ContinuedPrimeArchUpperAntiHerglotz := by
  intro z hzIm hzHalf hzeta
  by_cases hlow : |z.re| ≤ 4
  · exact continuedPrimeArchSourceRelativeTrace_im_nonpos_four
      z hzIm hzHalf hlow
  have habs : 4 < |z.re| := lt_of_not_ge hlow
  by_cases hpos : 4 < z.re
  · exact hhigh z hzIm hzHalf hpos hzeta
  have hneg : z.re < -4 := by
    have hzle : z.re ≤ 4 := le_of_not_gt hpos
    by_contra hn
    have hzneg : -4 ≤ z.re := le_of_not_gt hn
    exact hlow (abs_le.mpr ⟨hzneg, hzle⟩)
  let w : ℂ := -(starRingEnd ℂ) z
  have hwIm : w.im = z.im := by simp [w]
  have hwRe : w.re = -z.re := by simp [w]
  obtain ⟨hwzeta, htrace⟩ :=
    continuedPrimeArchSourceRelativeTrace_neg_conj_im z hzIm hzHalf hzeta
  have hsign := hhigh w (by rw [hwIm]; exact hzIm)
    (by rw [hwIm]; exact hzHalf) (by rw [hwRe]; linarith)
    (by simpa only [w] using hwzeta)
  rwa [htrace] at hsign

/-- High positive-frequency source accretivity proves RH. -/
theorem riemannHypothesis_of_continuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz
    (hhigh : ContinuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz) :
    RiemannHypothesis :=
  riemannHypothesis_of_continuedPrimeArchUpperAntiHerglotz
    (continuedPrimeArchUpperAntiHerglotz_of_positiveHighFrequency hhigh)

/-- RH supplies the full source sign, hence its high positive-frequency restriction. -/
theorem continuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ContinuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz := by
  intro z hzIm hzHalf _hzRe hzeta
  exact (continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis.mpr hRH)
    z hzIm hzHalf hzeta

/-- Exact one-sided high-frequency source criterion. -/
theorem continuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz_iff_riemannHypothesis :
    ContinuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_continuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz,
    continuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz_of_riemannHypothesis⟩

/-- Original-coordinate source condition: completed prime--Gamma accretivity is required only
above positive height four in the left half of the critical strip. -/
def CompletedPrimeGammaPositiveHighAccretive : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → 4 < s.im →
    riemannZeta s ≠ 0 → 0 ≤ (completedPrimeGammaFlux s).re

theorem continuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz_of_completedPrimeGamma
    (hacc : CompletedPrimeGammaPositiveHighAccretive) :
    ContinuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz := by
  intro z hzIm hzHalf hzRe hzeta
  let s : ℂ := 1 / 2 + z * I
  have hsRe : s.re = 1 / 2 - z.im := by
    simp [s, mul_re]
    ring
  have hsIm : s.im = z.re := by simp [s, mul_im]
  have hspos : 0 < s.re := by rw [hsRe]; linarith
  have hshalf : s.re < 1 / 2 := by rw [hsRe]; linarith
  have haccS := hacc s hspos hshalf (by rw [hsIm]; exact hzRe)
    (by simpa only [s] using hzeta)
  rw [continuedPrimeArchSourceRelativeTrace]
  change (-I * (infinitePrimeFlux s - logDeriv archFactor s)).im ≤ 0
  simp only [mul_im, I_re, zero_mul, neg_im, I_im, neg_mul, one_mul]
  dsimp only [completedPrimeGammaFlux] at haccS
  linarith

theorem completedPrimeGammaPositiveHighAccretive_of_continuedPrimeArch
    (hsource : ContinuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz) :
    CompletedPrimeGammaPositiveHighAccretive := by
  intro s hspos hshalf hsIm hzeta
  let z : ℂ := (s - 1 / 2) * (-I)
  have hcoord : 1 / 2 + z * I = s := by
    dsimp only [z]
    rw [mul_assoc]
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [hI, mul_one]
    ring
  have hzIm : z.im = 1 / 2 - s.re := by simp [z]
  have hzRe : z.re = s.im := by simp [z, mul_re]
  have hsourceZ := hsource z (by rw [hzIm]; linarith)
    (by rw [hzIm]; linarith) (by rw [hzRe]; exact hsIm)
    (by rw [hcoord]; exact hzeta)
  rw [continuedPrimeArchSourceRelativeTrace, hcoord] at hsourceZ
  change (-I * (infinitePrimeFlux s - logDeriv archFactor s)).im ≤ 0 at hsourceZ
  simp only [mul_im, I_re, zero_mul, neg_im, I_im, neg_mul, one_mul] at hsourceZ
  dsimp only [completedPrimeGammaFlux]
  linarith

theorem completedPrimeGammaPositiveHighAccretive_iff_centered :
    CompletedPrimeGammaPositiveHighAccretive ↔
      ContinuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz :=
  ⟨continuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz_of_completedPrimeGamma,
    completedPrimeGammaPositiveHighAccretive_of_continuedPrimeArch⟩

/-- Countable high-frequency source condition at Gaussian-rational points only. -/
def CompletedPrimeGammaGaussianRatPositiveHighAccretive : Prop :=
  ∀ q : ℚ × ℚ, 0 < (gaussianRatPoint q).re →
    (gaussianRatPoint q).re < 1 / 2 →
    4 < (gaussianRatPoint q).im →
    riemannZeta (gaussianRatPoint q) ≠ 0 →
      0 ≤ (completedPrimeGammaFlux (gaussianRatPoint q)).re

theorem completedPrimeGammaGaussianRatPositiveHighAccretive_of_full
    (hfull : CompletedPrimeGammaPositiveHighAccretive) :
    CompletedPrimeGammaGaussianRatPositiveHighAccretive := by
  intro q hq0 hqh hqIm hqz
  exact hfull (gaussianRatPoint q) hq0 hqh hqIm hqz

/-- Continuity and Gaussian-rational density recover the full high-frequency source condition
from the countable value family. -/
theorem completedPrimeGammaPositiveHighAccretive_of_gaussianRat
    (hrat : CompletedPrimeGammaGaussianRatPositiveHighAccretive) :
    CompletedPrimeGammaPositiveHighAccretive := by
  intro s hspos hshalf hsIm hzeta
  by_contra hnonneg
  have hneg : (completedPrimeGammaFlux s).re < 0 := lt_of_not_ge hnonneg
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [one_re] at hre
    linarith
  have hcont := continuousAt_completedPrimeGammaFlux hspos hs1 hzeta
  have hrePos : {w : ℂ | 0 < w.re} ∈ nhds s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hspos
  have hreHalf : {w : ℂ | w.re < 1 / 2} ∈ nhds s :=
    (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hshalf
  have himHigh : {w : ℂ | 4 < w.im} ∈ nhds s :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hsIm
  have hzetaAn : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs1
  have hzetaNe : {w : ℂ | riemannZeta w ≠ 0} ∈ nhds s :=
    hzetaAn.continuousAt.eventually_ne hzeta
  have hfre : ContinuousAt (fun w => (completedPrimeGammaFlux w).re) s :=
    Complex.continuous_re.continuousAt.comp hcont
  have hfluxNeg : {w : ℂ | (completedPrimeGammaFlux w).re < 0} ∈ nhds s :=
    hfre.tendsto (Iio_mem_nhds hneg)
  have hall : {w : ℂ | 0 < w.re} ∩ {w : ℂ | w.re < 1 / 2} ∩
      {w : ℂ | 4 < w.im} ∩ {w : ℂ | riemannZeta w ≠ 0} ∩
      {w : ℂ | (completedPrimeGammaFlux w).re < 0} ∈ nhds s :=
    inter_mem (inter_mem (inter_mem (inter_mem hrePos hreHalf) himHigh) hzetaNe)
      hfluxNeg
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hall
  obtain ⟨q, hqball⟩ := denseRange_gaussianRatPoint.exists_mem_open isOpen_ball
    ⟨s, mem_ball_self hr⟩
  have hq := hball hqball
  have hqnonneg := hrat q hq.1.1.1.1 hq.1.1.1.2 hq.1.1.2 hq.1.2
  exact (not_lt_of_ge hqnonneg) hq.2

/-- Exact countable positive-height source-value criterion for RH. -/
theorem completedPrimeGammaGaussianRatPositiveHighAccretive_iff_riemannHypothesis :
    CompletedPrimeGammaGaussianRatPositiveHighAccretive ↔ RiemannHypothesis := by
  constructor
  · intro hrat
    exact riemannHypothesis_of_continuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz
      (continuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz_of_completedPrimeGamma
        (completedPrimeGammaPositiveHighAccretive_of_gaussianRat hrat))
  · intro hRH
    exact completedPrimeGammaGaussianRatPositiveHighAccretive_of_full
      (completedPrimeGammaPositiveHighAccretive_of_continuedPrimeArch
        (continuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz_of_riemannHypothesis hRH))

end

end RHTower
