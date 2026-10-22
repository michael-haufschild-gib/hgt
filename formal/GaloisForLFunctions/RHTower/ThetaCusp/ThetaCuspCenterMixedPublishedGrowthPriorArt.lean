import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedOrientationRankUniversalityLaw
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGaussianHankelApertureWidthSpectrum
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspWignerProductFiberNormalForm
import GaloisForLFunctions.RHTower.XiHeatShellMinimum

/-!
# Published theta-kernel and horizontal Xi-growth prior art

This module records two published theorem surfaces needed to delimit the theta-cusp route.

* Sondow--Dumitrescu: a zero-free half-plane gives strict horizontal growth of `|Xi|`.
* Planat (June 2026): the theta-kernel current has an exact coupled-cone representation, its
  exterior strip is unconditionally nonnegative, and the remaining critical-aperture positivity
  is exactly the RH endpoint.

Nothing in this module is claimed as new scientific knowledge.  The strict result strengthens an
earlier nonnegative internal helper to the exact published strict statement.
-/

open Complex Set Metric Filter Topology MeasureTheory

namespace RHTower

noncomputable section

/-! ## Sondow--Dumitrescu strict horizontal Xi-modulus growth -/

/-- Every line-conjugate pair of relative-resolvent atoms is strictly Herglotz-positive below a
closed horizontal bound for the Xi divisor. -/
lemma xiRelativeResolventTerm_lineConj_pair_im_pos_of_halfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hzeros : XiZeroHalfPlaneBound alpha)
    (z : ℂ) (hzIm : z.im < -alpha) (q : XiZeroCopy) :
    0 < (xiRelativeResolventTerm z q +
      xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)).im := by
  let lam : ℂ := xiSpectralPoint q
  have hlamAbs : |lam.im| ≤ alpha := by
    rw [xiSpectralPoint_im_eq]
    simpa [abs_sub_comm] using
      abs_xiZero_re_sub_half_le_of_halfPlaneBound hzeros q
  have hAlphaMinus : 0 ≤ alpha - |lam.im| := sub_nonneg.mpr hlamAbs
  have hAlphaPlus : 0 ≤ alpha + |lam.im| := add_nonneg halpha (abs_nonneg _)
  have hlamSq : lam.im ^ (2 : ℕ) ≤ alpha ^ (2 : ℕ) := by
    have hprod := mul_nonneg hAlphaMinus hAlphaPlus
    nlinarith [sq_abs lam.im]
  have hzMinus : 0 < -z.im - alpha := by linarith
  have hzPlus : 0 < -z.im + alpha := by linarith
  have hzSq : alpha ^ (2 : ℕ) < z.im ^ (2 : ℕ) := by
    have hprod := mul_pos hzMinus hzPlus
    nlinarith
  have hcore : 0 < (z.re - lam.re) ^ (2 : ℕ) + z.im ^ (2 : ℕ) - lam.im ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (z.re - lam.re)]
  have hzlam : z ≠ lam := by
    intro h
    have him := congrArg Complex.im h
    have hlamLower : -alpha ≤ lam.im := (abs_le.mp hlamAbs).1
    linarith
  have hzlamc : z ≠ (starRingEnd ℂ) lam := by
    intro h
    have him := congrArg Complex.im h
    have hlamUpper : lam.im ≤ alpha := (abs_le.mp hlamAbs).2
    simp only [Complex.conj_im] at him
    linarith
  have hdenOne : 0 < (z.re - lam.re) ^ (2 : ℕ) + (z.im - lam.im) ^ (2 : ℕ) := by
    have h : z - lam ≠ 0 := sub_ne_zero.mpr hzlam
    simpa only [Complex.normSq_apply, sub_re, sub_im, pow_two] using
      Complex.normSq_pos.mpr h
  have hdenTwo : 0 < (z.re - lam.re) ^ (2 : ℕ) + (z.im + lam.im) ^ (2 : ℕ) := by
    have h : z - (starRingEnd ℂ) lam ≠ 0 := sub_ne_zero.mpr hzlamc
    simpa only [Complex.normSq_apply, Complex.conj_re, Complex.conj_im,
      sub_re, sub_im, sub_neg_eq_add, pow_two] using Complex.normSq_pos.mpr h
  rw [xiRelativeResolventTerm, xiRelativeResolventTerm, xiSpectralPoint_lineConj]
  change 0 < ((lam⁻¹ - (lam - z)⁻¹) +
      (((starRingEnd ℂ) lam)⁻¹ - ((starRingEnd ℂ) lam - z)⁻¹)).im
  rw [relativeResolvent_conj_pair_im_formula z lam
    (xiSpectralPoint_ne_zero q) hzlam (by simpa using hzlamc)]
  exact div_pos (mul_pos (by nlinarith [hzIm]) hcore) (mul_pos hdenOne hdenTwo)

/-- The full Xi relative-resolvent trace is strictly Herglotz-positive below every closed
horizontal divisor bound. -/
theorem xiRelativeResolventTrace_im_pos_of_halfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hzeros : XiZeroHalfPlaneBound alpha)
    (z : ℂ) (hzIm : z.im < -alpha) :
    0 < (xiRelativeResolventTrace z).im := by
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
  have hsum := summable_xiRelativeResolventTerm hXi
  have hsumJ : Summable (fun q : XiZeroCopy =>
      xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)) :=
    (xiZeroCopyLineConjEquiv.summable_iff).mpr hsum
  have hpair := hsum.add hsumJ
  have hpairIm : Summable (fun q : XiZeroCopy =>
      (xiRelativeResolventTerm z q +
        xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)).im) :=
    hpair.map Complex.imCLM Complex.imCLM.continuous
  let q0 : XiZeroCopy := Classical.choice nonempty_xiZeroCopy
  have hsumPos : 0 < ∑' q : XiZeroCopy,
      (xiRelativeResolventTerm z q +
        xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)).im :=
    hpairIm.tsum_pos
      (fun q =>
        (xiRelativeResolventTerm_lineConj_pair_im_pos_of_halfPlaneBound
          halpha hzeros z hzIm q).le)
      q0
      (xiRelativeResolventTerm_lineConj_pair_im_pos_of_halfPlaneBound
        halpha hzeros z hzIm q0)
  have heq := tsum_lineConj_pair_im_eq_two_mul_xiRelativeResolventTrace_im hXi
  linarith

/-- Strict positive Xi/Hedenmalm current at every aperture beyond a horizontal zero bound. -/
theorem thetaXiHankelOrbit_kreinForm_pos_of_halfPlaneBound
    {alpha a : ℝ} (halpha : 0 ≤ alpha) (hzeros : XiZeroHalfPlaneBound alpha)
    (ha : alpha < a) (b : ℝ) :
    0 < hedenmalmHankelKreinForm
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
    xiRelativeResolventTrace_im_pos_of_halfPlaneBound halpha hzeros z hzIm
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
  change 0 < 2 * (((starRingEnd ℂ) (XiC z)) * (-I * deriv XiC z)).re
  rw [kreinCurrent_eq_normSq_mul_logDeriv_im (XiC z) (deriv XiC z) hXi]
  rw [← logDeriv_apply, hlog]
  exact mul_pos (mul_pos (by norm_num) (Complex.normSq_pos.mpr hXi)) htrace

/-- Horizontal derivative statement in centered Xi coordinates. -/
theorem hasDerivAt_normSq_XiC_horizontalGrowth (a b : ℝ) :
    HasDerivAt
      (fun t : ℝ => Complex.normSq (XiC ((b : ℂ) - (t : ℂ) * I)))
      (hedenmalmHankelKreinForm
        (thetaXiHankelOrbitValuePlus a b)
        (thetaXiHankelOrbitTangentPlus a b)
        (thetaXiHankelOrbitValueMinus a b)
        (thetaXiHankelOrbitTangentMinus a b)) a := by
  simpa only [thetaXiHankelOrbitValuePlus] using
    hasDerivAt_thetaXiHankelOrbit_normSq a b

/-- **Sondow--Dumitrescu, squared-modulus form.** Under `Re rho ≤ 1/2 + alpha` for every Xi
zero, `|Xi(1/2+a+ib)|²` is strictly increasing in `a` on `[alpha,∞)`. -/
theorem strictMonoOn_normSq_XiC_horizontal_of_halfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hzeros : XiZeroHalfPlaneBound alpha)
    (b : ℝ) :
    StrictMonoOn
      (fun a : ℝ => Complex.normSq (XiC ((b : ℂ) - (a : ℂ) * I)))
      (Set.Ici alpha) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici alpha)
  · exact (Complex.continuous_normSq.comp
      (XiC_differentiable.continuous.comp (by fun_prop))).continuousOn
  · intro a ha
    rw [interior_Ici] at ha
    have hd := hasDerivAt_normSq_XiC_horizontalGrowth a b
    rw [hd.deriv]
    exact thetaXiHankelOrbit_kreinForm_pos_of_halfPlaneBound
      halpha hzeros ha b

/-- **Sondow--Dumitrescu, exact modulus form.** Under `Re rho ≤ 1/2 + alpha` for every Xi zero,
`|Xi(1/2+a+ib)|` is strictly increasing in `a` on `[alpha,∞)`. -/
theorem strictMonoOn_norm_XiC_horizontal_of_halfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hzeros : XiZeroHalfPlaneBound alpha)
    (b : ℝ) :
    StrictMonoOn
      (fun a : ℝ => ‖XiC ((b : ℂ) - (a : ℂ) * I)‖)
      (Set.Ici alpha) := by
  intro a ha c hc hac
  have hs := strictMonoOn_normSq_XiC_horizontal_of_halfPlaneBound
    halpha hzeros b ha hc hac
  change Complex.normSq (XiC ((b : ℂ) - (a : ℂ) * I)) <
    Complex.normSq (XiC ((b : ℂ) - (c : ℂ) * I)) at hs
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hs
  nlinarith [norm_nonneg (XiC ((b : ℂ) - (a : ℂ) * I)),
    norm_nonneg (XiC ((b : ℂ) - (c : ℂ) * I))]

/-! ## Planat theta-kernel representation and critical-aperture localization -/

/-- Positivity predicate for the exact coupled lower-cone theta kernel in the only unresolved
aperture `0 < a < 1/2`. -/
def PlanatThetaKernelCriticalApertureNonnegative : Prop :=
  ∀ (a : ℝ), 0 < a → a < 1 / 2 → ∀ b : ℝ,
    0 ≤ ∫ p : ℝ × ℝ in thetaCuspPositiveLowerCone,
      thetaCuspCofinalCoupledConeKernel a b p.1 p.2
        ∂((volume.restrict (Set.Ioi 0)).prod
          (volume.restrict (Set.Ioi 0)))

/-- The exact coupled-cone theta-kernel positivity in the critical aperture is equivalent to RH.
This is a formal ownership/localization theorem, not a new RH criterion claim. -/
theorem planatThetaKernelCriticalApertureNonnegative_iff_riemannHypothesis :
    PlanatThetaKernelCriticalApertureNonnegative ↔ RiemannHypothesis := by
  constructor
  · intro hkernel
    apply thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis.mp
    intro a ha ha0 haHalf b
    have hk := hkernel a ha0 haHalf b
    change 0 ≤ thetaCuspCenterMixedFourierCurrent a ha b
    rw [thetaCuspCenterMixedFourierCurrent_eq_sixteen_mul_coupledCone
      ha0.le haHalf b]
    exact mul_nonneg (by norm_num) hk
  · intro hRH a ha0 haHalf b
    have hcurrent :=
      thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis.mpr hRH
        a (by rw [abs_of_pos ha0]; linarith) ha0 haHalf b
    change 0 ≤ thetaCuspCenterMixedFourierCurrent a
      (by rw [abs_of_pos ha0]; linarith) b at hcurrent
    rw [thetaCuspCenterMixedFourierCurrent_eq_sixteen_mul_coupledCone
      ha0.le haHalf b] at hcurrent
    nlinarith

/-- **Planat localization package.** The actual current is the exact coupled theta-kernel in
`0 ≤ a < 1/2`, is unconditionally nonnegative in `1/2 ≤ a < 1`, and the remaining kernel
positivity is exactly RH. -/
theorem thetaCuspCenterMixed_publishedGrowthLocalization_package :
    (∀ (a : ℝ) (ha0 : 0 ≤ a) (haHalf : a < 1 / 2) (b : ℝ),
      thetaCuspCenterMixedFourierCurrent a
          (by rw [abs_of_nonneg ha0]; linarith) b =
        16 * ∫ p : ℝ × ℝ in thetaCuspPositiveLowerCone,
          thetaCuspCofinalCoupledConeKernel a b p.1 p.2
            ∂((volume.restrict (Set.Ioi 0)).prod
              (volume.restrict (Set.Ioi 0)))) ∧
    (∀ (a : ℝ) (haHalf : 1 / 2 ≤ a) (haOne : a < 1) (b : ℝ),
      0 ≤ thetaCuspCenterMixedFourierCurrent a
        (by rw [abs_of_nonneg (by linarith : 0 ≤ a)]; exact haOne) b) ∧
    (PlanatThetaKernelCriticalApertureNonnegative ↔ RiemannHypothesis) := by
  refine ⟨?_, ?_, planatThetaKernelCriticalApertureNonnegative_iff_riemannHypothesis⟩
  · intro a ha0 haHalf b
    exact thetaCuspCenterMixedFourierCurrent_eq_sixteen_mul_coupledCone
      ha0 haHalf b
  · intro a haHalf haOne b
    exact thetaCuspCenterMixedFourierCurrent_nonneg_of_half_le
      haHalf haOne b

end

end RHTower
