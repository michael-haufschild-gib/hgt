import GaloisForLFunctions.RHTower.HedenmalmExteriorGaussianHankel
import GaloisForLFunctions.RHTower.XiThermalProjectiveMomentSpectrum
import Mathlib.Analysis.Convex.Deriv

/-!
# The complete Hedenmalm Hankel threshold is the Xi divisor width

For a nonnegative transverse scale `alpha`, positivity of every complete Gaussian-windowed
Hedenmalm Hankel tower at every aperture strictly above `alpha` is equivalent to the assertion
that every Xi zero lies in the half-plane `Re rho ≤ 1/2 + alpha`.  Thus the full positivity phase
transition, rather than only its RH endpoint, is exactly the horizontal support radius of the Xi
divisor.

The proof is unconditional.  The forward direction pairs every Xi relative-resolvent atom with
its critical-line conjugate.  The reverse direction uses the exact aperture derivative of the Xi
modulus and isolation of the Xi divisor.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- Positivity of every complete Gaussian Hedenmalm tower at apertures strictly above `alpha`. -/
def HedenmalmGaussianHankelTailCone (tau alpha : ℝ) : Prop :=
  ∀ (a : ℝ) (ha : |a| < 1), alpha < a →
    CompleteHankelCone
      (weightedMoment (gaussianWindowMeasure tau)
        (thetaCuspCenterMixedFourierCurrent a ha))

/-- Under a Xi half-plane bound, every line-conjugate pair of relative-resolvent atoms has the
lower-half-plane Herglotz sign strictly below the corresponding transverse width. -/
lemma xiRelativeResolventTerm_lineConj_pair_im_nonneg_of_halfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hzeros : XiZeroHalfPlaneBound alpha)
    (z : ℂ) (hzIm : z.im < -alpha) (q : XiZeroCopy) :
    0 ≤ (xiRelativeResolventTerm z q +
      xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)).im := by
  let lam : ℂ := xiSpectralPoint q
  have hlamAbs : |lam.im| ≤ alpha := by
    rw [xiSpectralPoint_im_eq]
    simpa [abs_sub_comm] using
      abs_xiZero_re_sub_half_le_of_halfPlaneBound hzeros q
  have hlamLower : -alpha ≤ lam.im := (abs_le.mp hlamAbs).1
  have hlamUpper : lam.im ≤ alpha := (abs_le.mp hlamAbs).2
  have hAlphaMinus : 0 ≤ alpha - |lam.im| := sub_nonneg.mpr hlamAbs
  have hAlphaPlus : 0 ≤ alpha + |lam.im| :=
    add_nonneg halpha (abs_nonneg _)
  have hlamSq : lam.im ^ 2 ≤ alpha ^ 2 := by
    have hprod := mul_nonneg hAlphaMinus hAlphaPlus
    nlinarith [sq_abs lam.im]
  have hzMinus : 0 < -z.im - alpha := by linarith
  have hzPlus : 0 < -z.im + alpha := by linarith
  have hzSq : alpha ^ 2 < z.im ^ 2 := by
    have hprod := mul_pos hzMinus hzPlus
    nlinarith
  have hcore : 0 < (z.re - lam.re) ^ 2 + z.im ^ 2 - lam.im ^ 2 := by
    nlinarith [sq_nonneg (z.re - lam.re)]
  have hzlam : z ≠ lam := by
    intro h
    have him := congrArg Complex.im h
    linarith
  have hzlamc : z ≠ (starRingEnd ℂ) lam := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.conj_im] at him
    linarith
  have hdenOne :
      0 < (z.re - lam.re) ^ 2 + (z.im - lam.im) ^ 2 := by
    have h : z - lam ≠ 0 := sub_ne_zero.mpr hzlam
    simpa only [Complex.normSq_apply, sub_re, sub_im, pow_two] using
      Complex.normSq_pos.mpr h
  have hdenTwo :
      0 < (z.re - lam.re) ^ 2 + (z.im + lam.im) ^ 2 := by
    have h : z - (starRingEnd ℂ) lam ≠ 0 := sub_ne_zero.mpr hzlamc
    simpa only [Complex.normSq_apply, Complex.conj_re, Complex.conj_im,
      sub_re, sub_im, sub_neg_eq_add, pow_two] using Complex.normSq_pos.mpr h
  rw [xiRelativeResolventTerm, xiRelativeResolventTerm,
    xiSpectralPoint_lineConj]
  change 0 ≤ ((lam⁻¹ - (lam - z)⁻¹) +
      (((starRingEnd ℂ) lam)⁻¹ - ((starRingEnd ℂ) lam - z)⁻¹)).im
  rw [relativeResolvent_conj_pair_im_formula z lam
    (xiSpectralPoint_ne_zero q) hzlam (by simpa using hzlamc)]
  exact div_nonneg
    (mul_nonneg (by nlinarith [hzIm]) hcore.le)
    (mul_nonneg hdenOne.le hdenTwo.le)

/-- The full Xi relative-resolvent trace has nonnegative imaginary part strictly below every
horizontal Xi divisor bound. -/
theorem xiRelativeResolventTrace_im_nonneg_of_halfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hzeros : XiZeroHalfPlaneBound alpha)
    (z : ℂ) (hzIm : z.im < -alpha) :
    0 ≤ (xiRelativeResolventTrace z).im := by
  have hXi : XiC z ≠ 0 := by
    intro hz
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp hz
    have hqAbs : |(xiSpectralPoint q).im| ≤ alpha := by
      rw [xiSpectralPoint_im_eq]
      simpa [abs_sub_comm] using
        abs_xiZero_re_sub_half_le_of_halfPlaneBound hzeros q
    have hqLower : -alpha ≤ (xiSpectralPoint q).im := (abs_le.mp hqAbs).1
    have him := congrArg Complex.im hq
    linarith
  have himsum :
      0 ≤ (∑' q : XiZeroCopy,
        (xiRelativeResolventTerm z q +
          xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)).im) :=
    tsum_nonneg fun q =>
      xiRelativeResolventTerm_lineConj_pair_im_nonneg_of_halfPlaneBound
        halpha hzeros z hzIm q
  linarith [tsum_lineConj_pair_im_eq_two_mul_xiRelativeResolventTrace_im hXi]

/-- A Xi half-plane bound places the actual theta/Xi orbit in the nonnegative Krein chamber at
every strictly larger aperture. -/
theorem thetaXiHankelOrbit_kreinForm_nonneg_of_halfPlaneBound
    {alpha a : ℝ} (halpha : 0 ≤ alpha) (hzeros : XiZeroHalfPlaneBound alpha)
    (ha : alpha < a) (b : ℝ) :
    0 ≤ hedenmalmHankelKreinForm
      (thetaXiHankelOrbitValuePlus a b)
      (thetaXiHankelOrbitTangentPlus a b)
      (thetaXiHankelOrbitValueMinus a b)
      (thetaXiHankelOrbitTangentMinus a b) := by
  let z : ℂ := (b : ℂ) - (a : ℂ) * I
  have hzIm : z.im < -alpha := by
    simp only [z, sub_im, ofReal_im, mul_im, I_re, I_im, ofReal_re,
      zero_mul, mul_one, zero_sub]
    linarith
  have htrace :=
    xiRelativeResolventTrace_im_nonneg_of_halfPlaneBound halpha hzeros z hzIm
  have hXi : XiC z ≠ 0 := by
    intro hz
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp hz
    have hqAbs : |(xiSpectralPoint q).im| ≤ alpha := by
      rw [xiSpectralPoint_im_eq]
      simpa [abs_sub_comm] using
        abs_xiZero_re_sub_half_le_of_halfPlaneBound hzeros q
    have hqLower : -alpha ≤ (xiSpectralPoint q).im := (abs_le.mp hqAbs).1
    have him := congrArg Complex.im hq
    linarith
  have hlog := logDeriv_XiC_eq_relativeResolventTrace hXi
  rw [thetaXiHankelOrbit_kreinForm_eq]
  rw [thetaXiHankelOrbitValuePlus, thetaXiHankelOrbitTangentPlus]
  change 0 ≤ 2 * (((starRingEnd ℂ) (XiC z)) * (-I * deriv XiC z)).re
  rw [kreinCurrent_eq_normSq_mul_logDeriv_im (XiC z) (deriv XiC z) hXi]
  rw [← logDeriv_apply, hlog]
  exact mul_nonneg (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)) htrace

/-- The Hedenmalm Fourier current is pointwise nonnegative at every aperture strictly beyond a
global Xi half-plane bound. -/
theorem thetaCuspCenterMixedFourierCurrent_nonneg_of_halfPlaneBound
    {alpha a : ℝ} (halpha : 0 ≤ alpha) (hzeros : XiZeroHalfPlaneBound alpha)
    (ha : alpha < a) (haOne : a < 1) (b : ℝ) :
    0 ≤ thetaCuspCenterMixedFourierCurrent a
      (by rw [abs_of_nonneg (halpha.trans (le_of_lt ha))]; exact haOne) b := by
  rw [thetaCuspCenterMixedFourierCurrent,
    fourier_thetaCuspHorizontalAutocorrelationTangent_scaled_eq_kreinForm]
  exact thetaXiHankelOrbit_kreinForm_nonneg_of_halfPlaneBound
    halpha hzeros ha b

/-- A Xi half-plane bound implies every complete Gaussian Hedenmalm tower strictly above that
transverse scale. -/
theorem hedenmalmGaussianHankelTailCone_of_xiZeroHalfPlaneBound
    {tau alpha : ℝ} (htau : 0 < tau) (halpha : 0 ≤ alpha)
    (hzeros : XiZeroHalfPlaneBound alpha) :
    HedenmalmGaussianHankelTailCone tau alpha := by
  intro a ha haAlpha
  have haPos : 0 < a := lt_of_le_of_lt halpha haAlpha
  have haOne : a < 1 := (abs_lt.mp ha).2
  apply (hedenmalmGaussianHankelCone_at_iff_pointwise htau ha).mpr
  intro b
  simpa only using thetaCuspCenterMixedFourierCurrent_nonneg_of_halfPlaneBound
    halpha hzeros haAlpha haOne b

/-- Tail positivity forces the corresponding Xi half-plane bound.  A zero beyond the threshold
would make the squared Xi modulus nondecreasing up to an isolated zero. -/
theorem xiZeroHalfPlaneBound_of_hedenmalmGaussianHankelTailCone
    {tau alpha : ℝ} (htau : 0 < tau) (halpha : 0 ≤ alpha)
    (htail : HedenmalmGaussianHankelTailCone tau alpha) :
    XiZeroHalfPlaneBound alpha := by
  intro rho hzero
  by_contra hnot
  have hrhoBound : 1 / 2 + alpha < rho.re := lt_of_not_ge hnot
  let d : ℝ := rho.re - 1 / 2
  let b : ℝ := rho.im
  have hdAlpha : alpha < d := by dsimp only [d]; linarith
  have hdPos : 0 < d := lt_of_le_of_lt halpha hdAlpha
  have hrhoPos : 0 < rho.re := by linarith
  have hrhoOne : rho.re < 1 := xi_zero_re_lt_one hrhoPos hzero
  have hdHalf : d < 1 / 2 := by dsimp only [d]; linarith
  let z0 : ℂ := (b : ℂ) - (d : ℂ) * I
  have hz0 : XiC z0 = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z0 * I = rho := by
      apply Complex.ext
      · simp [z0, b, d, mul_re]
      · simp [z0, b, d, mul_im]
    rw [harg, hzero]
  obtain ⟨gap, hgap, hgapSpec⟩ := exists_xiSpectralPoint_gap z0
  let eta : ℝ := min ((d - alpha) / 2) (gap / 2)
  have hetaPos : 0 < eta := by
    dsimp only [eta]
    exact lt_min (half_pos (sub_pos.mpr hdAlpha)) (half_pos hgap)
  have hetaAlpha : eta ≤ (d - alpha) / 2 := min_le_left _ _
  have hetaGap : eta < gap := by
    exact (min_le_right ((d - alpha) / 2) (gap / 2)).trans_lt (half_lt_self hgap)
  let c : ℝ := d - eta
  have hcAlpha : alpha < c := by
    dsimp only [c]
    nlinarith
  have hcD : c < d := by dsimp only [c]; linarith
  have hcPos : 0 < c := lt_of_le_of_lt halpha hcAlpha
  have hcOne : c < 1 := by linarith
  have hdOne : d < 1 := by linarith
  have hcAbs : |c| < 1 := by rw [abs_of_pos hcPos]; exact hcOne
  let zc : ℂ := (b : ℂ) - (c : ℂ) * I
  have hdist : ‖zc - z0‖ = eta := by
    have hdiff : zc - z0 = (eta : ℂ) * I := by
      dsimp only [zc, z0, c]
      push_cast
      ring
    rw [hdiff, norm_mul]
    simp [Real.norm_eq_abs, abs_of_pos hetaPos]
  have hzcNe : zc ≠ z0 := by
    intro h
    have hnorm : ‖zc - z0‖ = 0 := by rw [h, sub_self, norm_zero]
    rw [hdist] at hnorm
    linarith
  have hzcXi : XiC zc ≠ 0 := by
    intro hzeroC
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy zc).mp hzeroC
    have hqNe : xiSpectralPoint q ≠ z0 := by
      rw [hq]
      exact hzcNe
    have hlower := hgapSpec q hqNe
    rw [hq, hdist] at hlower
    linarith
  let U : ℝ → ℝ := fun x =>
    Complex.normSq (thetaXiHankelOrbitValuePlus x b)
  have hUderiv (x : ℝ) : HasDerivAt U
      (hedenmalmHankelKreinForm
        (thetaXiHankelOrbitValuePlus x b)
        (thetaXiHankelOrbitTangentPlus x b)
        (thetaXiHankelOrbitValueMinus x b)
        (thetaXiHankelOrbitTangentMinus x b)) x := by
    simpa only [U] using hasDerivAt_thetaXiHankelOrbit_normSq x b
  have hmono : MonotoneOn U (Icc c d) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc c d)
    · intro x hx
      exact (hUderiv x).continuousAt.continuousWithinAt
    · intro x hx
      exact (hUderiv x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hUderiv x).deriv]
      have hxAlpha : alpha < x := hcAlpha.trans hx.1
      have hxPos : 0 < x := lt_of_le_of_lt halpha hxAlpha
      have hxOne : x < 1 := hx.2.trans hdOne
      have hxAbs : |x| < 1 := by rw [abs_of_pos hxPos]; exact hxOne
      have hpoint := (hedenmalmGaussianHankelCone_at_iff_pointwise htau hxAbs).mp
        (htail x hxAbs hxAlpha) b
      rw [thetaCuspCenterMixedFourierCurrent,
        fourier_thetaCuspHorizontalAutocorrelationTangent_scaled_eq_kreinForm] at hpoint
      simpa using hpoint
  have hcd : U c ≤ U d := hmono ⟨le_rfl, hcD.le⟩ ⟨hcD.le, le_rfl⟩ hcD.le
  have hUd : U d = 0 := by
    unfold U thetaXiHankelOrbitValuePlus
    rw [show (b : ℂ) - (d : ℂ) * I = z0 by rfl, hz0]
    simp
  have hUcPos : 0 < U c := by
    unfold U thetaXiHankelOrbitValuePlus
    rw [show (b : ℂ) - (c : ℂ) * I = zc by rfl]
    exact Complex.normSq_pos.mpr hzcXi
  rw [hUd] at hcd
  linarith

/-- **Complete aperture--width phase law.**  At any positive Gaussian temperature, the first
aperture above which every complete Hedenmalm Hankel tower is positive is exactly the horizontal
support width of the Xi divisor. -/
theorem hedenmalmGaussianHankelTailCone_iff_xiZeroHalfPlaneBound
    {tau alpha : ℝ} (htau : 0 < tau) (halpha : 0 ≤ alpha) :
    HedenmalmGaussianHankelTailCone tau alpha ↔ XiZeroHalfPlaneBound alpha := by
  constructor
  · exact xiZeroHalfPlaneBound_of_hedenmalmGaussianHankelTailCone htau halpha
  · exact hedenmalmGaussianHankelTailCone_of_xiZeroHalfPlaneBound htau halpha

/-- The tail phase law is independent of the chosen positive Gaussian temperature. -/
theorem hedenmalmGaussianHankelTailCone_temperature_iff
    {tau sigma alpha : ℝ} (htau : 0 < tau) (hsigma : 0 < sigma)
    (halpha : 0 ≤ alpha) :
    HedenmalmGaussianHankelTailCone tau alpha ↔
      HedenmalmGaussianHankelTailCone sigma alpha :=
  (hedenmalmGaussianHankelTailCone_iff_xiZeroHalfPlaneBound htau halpha).trans
    (hedenmalmGaussianHankelTailCone_iff_xiZeroHalfPlaneBound hsigma halpha).symm

/-- At threshold zero, the complete aperture-width phase law specializes exactly to RH. -/
theorem hedenmalmGaussianHankelTailCone_zero_iff_riemannHypothesis
    {tau : ℝ} (htau : 0 < tau) :
    HedenmalmGaussianHankelTailCone tau 0 ↔ RiemannHypothesis := by
  rw [hedenmalmGaussianHankelTailCone_iff_xiZeroHalfPlaneBound htau (le_refl 0)]
  constructor
  · intro hzeros
    rw [rh_iff_xi_ne_zero_right]
    intro rho hrho hzero
    have hbound := hzeros rho hzero
    rw [mem_rightHalf] at hrho
    norm_num at hbound
    linarith
  · intro hRH rho hzero
    rw [xi_zero_re_eq_half_of_RH hRH hzero]
    norm_num

end

end RHTower
