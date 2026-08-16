import GaloisForLFunctions.RHTower.XiMassBesselHeightDerivative

/-!
# The differentiated exterior envelope

Outside a fixed slope cone `h ≥ κu` the mass Fourier profile is differentiable in the height and
its derivative obeys the same envelope as the profile:

`|F_u'(h)| ≤ C u^{-1/2} e^{-a√(h²−u²)}`.

Both statements follow from the Fourier–Bessel identity: the derivative is the closed expression
`2aτ h (a K₁'(az) z − K₁(az))/z³`, in which the three ratios `‖τ‖/‖z‖`, `h/‖z‖`, `1/‖z‖` are
bounded by cone constants and both Schläfli envelopes carry the same exponential decay with the
same square-root gain.

Adding the damping factor `e^{-h/2}` gives the differentiated envelope of the damped profile,
`|G_u(h)| + |G_u'(h)| ≤ C₀ u^{-1/2} e^{-h/2 − a√(h²−u²)}`.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## Differentiability of the profile in the height -/

theorem xiMassStripMem_of_lt {sigma u t : ℝ} (hsigma : 0 < sigma) (hu : 0 ≤ u) (ht : u < t) :
    ((sigma : ℂ) + (u : ℂ) * I) ∈ xiMassBesselStrip t := by
  constructor
  · simpa using hsigma
  · have him : ((sigma : ℂ) + (u : ℂ) * I).im = u := by simp
    rw [him, abs_of_nonneg hu]
    exact ht

/-- **The mass Fourier profile is differentiable in the height outside the light cone.** -/
theorem hasDerivAt_stripFourier_xiMass {a sigma u h : ℝ} (ha : 0 < a) (hsigma : 0 < sigma)
    (hu : 0 ≤ u) (huh : u < h) :
    HasDerivAt
      (fun t : ℝ => stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (t : ℂ))
      (xiMassBesselHeightDeriv a ((sigma : ℂ) + (u : ℂ) * I) (h : ℂ)) h := by
  have hpos : 0 < (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2).re :=
    xiMassPropagation_re_pos (xiMassStripMem_of_lt hsigma hu huh)
  have hbase : HasDerivAt
      (fun t : ℝ => xiMassBesselHeightSide a ((sigma : ℂ) + (u : ℂ) * I) (t : ℂ))
      (xiMassBesselHeightDeriv a ((sigma : ℂ) + (u : ℂ) * I) (h : ℂ)) h :=
    (hasDerivAt_xiMassBesselHeightSide ha hpos).comp_ofReal
  refine hbase.congr_of_eventuallyEq ?_
  have hnb : {t : ℝ | u < t} ∈ nhds h :=
    (isOpen_lt continuous_const continuous_id).mem_nhds huh
  filter_upwards [hnb] with t ht
  show stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (t : ℂ)
      = xiMassBesselHeightSide a ((sigma : ℂ) + (u : ℂ) * I) (t : ℂ)
  rw [xiMassBesselHeightSide_ofReal]
  exact stripFourier_xiMass_eq_bessel ha (lt_of_le_of_lt hu ht)
    (xiMassStripMem_of_lt hsigma hu ht)

/-- The height derivative of the damped mass profile. -/
def xiMassCriticalDampedFourierProfileDeriv (a sigma u h : ℝ) : ℂ :=
  (Real.exp (-h / 2) : ℂ)
    * (xiMassBesselHeightDeriv a ((sigma : ℂ) + (u : ℂ) * I) (h : ℂ)
      - (1 / 2 : ℂ) * stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ))

/-- **The damped profile is differentiable in the height outside the light cone.** -/
theorem hasDerivAt_xiMassCriticalDampedFourierProfile {a sigma u h : ℝ} (ha : 0 < a)
    (hsigma : 0 < sigma) (hu : 0 ≤ u) (huh : u < h) :
    HasDerivAt (fun t : ℝ => xiMassCriticalDampedFourierProfile a sigma u t)
      (xiMassCriticalDampedFourierProfileDeriv a sigma u h) h := by
  have hF := hasDerivAt_stripFourier_xiMass ha hsigma hu huh
  have hexp : HasDerivAt (fun t : ℝ => ((Real.exp (-t / 2) : ℝ) : ℂ))
      (((Real.exp (-h / 2) * -(1 / 2) : ℝ) : ℂ)) h := by
    have h2 : HasDerivAt (fun t : ℝ => -t / 2) (-(1 / 2)) h := by
      simpa using ((hasDerivAt_id h).neg.div_const 2)
    exact (h2.exp).ofReal_comp
  have hprod := hexp.mul hF
  have heq : ((Real.exp (-h / 2) * -(1 / 2) : ℝ) : ℂ)
        * stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ)
      + ((Real.exp (-h / 2) : ℝ) : ℂ)
        * xiMassBesselHeightDeriv a ((sigma : ℂ) + (u : ℂ) * I) (h : ℂ)
      = xiMassCriticalDampedFourierProfileDeriv a sigma u h := by
    rw [xiMassCriticalDampedFourierProfileDeriv]
    push_cast
    ring
  rw [← heq]
  exact hprod

/-! ## The exterior envelope of the height derivative -/

/-- The exterior envelope constant of the height derivative. -/
def xiMassBesselDerivExteriorSqrtConstant (a sigma kappa : ℝ) : ℝ :=
  2 * a * (1 + 1 / Real.sqrt (kappa ^ 2 - 1)) * (kappa / Real.sqrt (kappa ^ 2 - 1))
    * (a + 1 / sigma) * Real.exp (2 / (a * sigma))
    * Real.sqrt (2 * Real.pi / (a * Real.sqrt (kappa ^ 2 - 1)))

theorem xiMassBesselDerivExteriorSqrtConstant_nonneg {a sigma kappa : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) :
    0 ≤ xiMassBesselDerivExteriorSqrtConstant a sigma kappa := by
  have hkappa2 : (0 : ℝ) < kappa ^ 2 - 1 := by nlinarith
  have hs : (0 : ℝ) < Real.sqrt (kappa ^ 2 - 1) := Real.sqrt_pos.2 hkappa2
  rw [xiMassBesselDerivExteriorSqrtConstant]
  have h1 : (0 : ℝ) ≤ 1 + 1 / Real.sqrt (kappa ^ 2 - 1) := by positivity
  have h2 : (0 : ℝ) ≤ kappa / Real.sqrt (kappa ^ 2 - 1) := by positivity
  have h3 : (0 : ℝ) ≤ a + 1 / sigma := by positivity
  have h4 : (0 : ℝ) ≤ 2 * a := by positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h4 h1) h2) h3)
    (Real.exp_nonneg _)) (Real.sqrt_nonneg _)

/-- **(19.2) The exterior envelope of the height derivative.** -/
theorem norm_xiMassBesselHeightDeriv_le {a sigma kappa u h : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hu : 0 < u) (hcone : kappa * u ≤ h) :
    ‖xiMassBesselHeightDeriv a ((sigma : ℂ) + (u : ℂ) * I) (h : ℂ)‖
      ≤ xiMassBesselDerivExteriorSqrtConstant a sigma kappa / Real.sqrt u
        * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hkappa2 : (0 : ℝ) < kappa ^ 2 - 1 := by nlinarith
  have hsq : (0 : ℝ) < Real.sqrt (kappa ^ 2 - 1) := Real.sqrt_pos.2 hkappa2
  have hsqsq : Real.sqrt (kappa ^ 2 - 1) ^ 2 = kappa ^ 2 - 1 := Real.sq_sqrt hkappa2.le
  have huh : u ≤ h := le_trans (by nlinarith) hcone
  have hh : 0 < h := lt_of_lt_of_le hu huh
  have hprop : ((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2
      = xiMassSpacelikePropagationArgument sigma u h :=
    (xiMassSpacelikePropagationArgument_eq sigma u h).symm
  have hzre : (HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)).re
      = HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h) := by
    rw [HTGeometry.csqrt_re, hprop]
  have hKsig : sigma ≤ HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h) :=
    sigma_le_csqrtRe_propagationArgument hsigma hu.le huh
  have hKpos : (0 : ℝ) < HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h) :=
    lt_of_lt_of_le hsigma hKsig
  have hKgap : Real.sqrt (h ^ 2 - u ^ 2)
      ≤ HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h) := by
    refine le_trans ?_ (sqrt_fullGap_le_csqrtRe_propagationArgument hsigma hu.le huh)
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hKslope : Real.sqrt (kappa ^ 2 - 1) * u
      ≤ HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h) :=
    sqrt_slopeGap_mul_le_csqrtRe_propagationArgument hsigma hkappa hu.le hcone
  have hzn : HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h)
      ≤ ‖HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)‖ := by
    rw [← hzre]
    exact Complex.re_le_norm _
  have hznpos : (0 : ℝ) < ‖HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)‖ :=
    lt_of_lt_of_le hKpos hzn
  have hzrepos : 0 < (HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)).re := by
    rw [hzre]; exact hKpos
  -- the two Schläfli envelopes at the shared exterior rate
  have hXre : ((a : ℂ) * HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)).re
      = a * HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h) := by
    rw [Complex.mul_re, hzre]
    simp
  have hX : 0 < ((a : ℂ) * HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)).re := by
    rw [hXre]; exact mul_pos ha hKpos
  have hE2 := HTGeometry.norm_besselK1CDeriv_le hX
  have hE1base := HTGeometry.norm_besselK1C_le hX
  rw [hXre] at hE2 hE1base
  have hE1 : ‖HTGeometry.besselK1C
      ((a : ℂ) * HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2))‖
      ≤ Real.exp (-(a * HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h)))
        * Real.exp (2 / (a * HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h)))
        * Real.sqrt (2 * Real.pi
            / (a * HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h))) := by
    refine hE1base.trans ?_
    have hmono : Real.exp (1 / (2 * (a * HTGeometry.csqrtRe
          (xiMassSpacelikePropagationArgument sigma u h))))
        ≤ Real.exp (2 / (a * HTGeometry.csqrtRe
          (xiMassSpacelikePropagationArgument sigma u h))) := by
      refine Real.exp_le_exp.2 ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos ha hKpos]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmono (Real.exp_nonneg _)) (Real.sqrt_nonneg _)
  have hEnn : (0 : ℝ) ≤ Real.exp (-(a * HTGeometry.csqrtRe
        (xiMassSpacelikePropagationArgument sigma u h)))
      * Real.exp (2 / (a * HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h)))
      * Real.sqrt (2 * Real.pi
          / (a * HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h))) := by
    positivity
  rw [xiMassBesselHeightDeriv]
  refine (norm_besselHeightDerivCore_le (t := h) ha hzrepos hEnn hE1 hE2).trans ?_
  -- the cone ratios
  have hτ : ‖(sigma : ℂ) + (u : ℂ) * I‖ ≤ sigma + u := by
    have hb := Complex.norm_le_abs_re_add_abs_im ((sigma : ℂ) + (u : ℂ) * I)
    have hre : ((sigma : ℂ) + (u : ℂ) * I).re = sigma := by simp
    have him : ((sigma : ℂ) + (u : ℂ) * I).im = u := by simp
    rw [hre, him, abs_of_pos hsigma, abs_of_pos hu] at hb
    exact hb
  have hratio1 : ‖(sigma : ℂ) + (u : ℂ) * I‖
      / ‖HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)‖
      ≤ 1 + 1 / Real.sqrt (kappa ^ 2 - 1) := by
    rw [div_le_iff₀ hznpos]
    have hsigK : sigma ≤ ‖HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)‖ :=
      le_trans hKsig hzn
    have hslopeK : Real.sqrt (kappa ^ 2 - 1) * u
        ≤ ‖HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)‖ :=
      le_trans hKslope hzn
    have hu' : u ≤ 1 / Real.sqrt (kappa ^ 2 - 1)
        * ‖HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)‖ := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hsq]
      linarith [hslopeK]
    linarith [hτ, hsigK, hu']
  have hratio2 : |h| / ‖HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)‖
      ≤ kappa / Real.sqrt (kappa ^ 2 - 1) := by
    rw [div_le_div_iff₀ hznpos hsq, abs_of_pos hh]
    have hgapK : Real.sqrt (h ^ 2 - u ^ 2)
        ≤ ‖HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)‖ :=
      le_trans hKgap hzn
    have hlow : h * Real.sqrt (kappa ^ 2 - 1) / kappa ≤ Real.sqrt (h ^ 2 - u ^ 2) := by
      have hnn : (0 : ℝ) ≤ h * Real.sqrt (kappa ^ 2 - 1) / kappa := by positivity
      have hsqle : (h * Real.sqrt (kappa ^ 2 - 1) / kappa) ^ 2 ≤ h ^ 2 - u ^ 2 := by
        have hex : (h * Real.sqrt (kappa ^ 2 - 1) / kappa) ^ 2
            = h ^ 2 * (kappa ^ 2 - 1) / kappa ^ 2 := by
          field_simp
          nlinarith [hsqsq]
        rw [hex, div_le_iff₀ (by positivity : (0:ℝ) < kappa ^ 2)]
        nlinarith [hcone, hu.le, hh.le]
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ h ^ 2 - u ^ 2 by nlinarith),
        Real.sqrt_nonneg (h ^ 2 - u ^ 2), hnn]
    have hfinal : h * Real.sqrt (kappa ^ 2 - 1) ≤ kappa
        * ‖HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)‖ := by
      have := le_trans hlow hgapK
      rw [div_le_iff₀ hkappa0] at this
      linarith [this]
    linarith [hfinal]
  have hratio3 : a + 1 / (HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)).re
      ≤ a + 1 / sigma := by
    rw [hzre]
    have := one_div_le_one_div_of_le hsigma hKsig
    linarith
  have hEbound : Real.exp (-(a * HTGeometry.csqrtRe
        (xiMassSpacelikePropagationArgument sigma u h)))
      * Real.exp (2 / (a * HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h)))
      * Real.sqrt (2 * Real.pi
          / (a * HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h)))
      ≤ Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) * Real.exp (2 / (a * sigma))
        * (Real.sqrt (2 * Real.pi / (a * Real.sqrt (kappa ^ 2 - 1))) / Real.sqrt u) := by
    have h1 : Real.exp (-(a * HTGeometry.csqrtRe
        (xiMassSpacelikePropagationArgument sigma u h)))
        ≤ Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) :=
      Real.exp_le_exp.2 (by nlinarith [hKgap])
    have h2 : Real.exp (2 / (a * HTGeometry.csqrtRe
        (xiMassSpacelikePropagationArgument sigma u h)))
        ≤ Real.exp (2 / (a * sigma)) := by
      refine Real.exp_le_exp.2 ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hKsig, hsigma, ha]
    have h3 : Real.sqrt (2 * Real.pi
          / (a * HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h)))
        ≤ Real.sqrt (2 * Real.pi / (a * Real.sqrt (kappa ^ 2 - 1))) / Real.sqrt u := by
      have hval : Real.sqrt (2 * Real.pi / (a * Real.sqrt (kappa ^ 2 - 1))) / Real.sqrt u
          = Real.sqrt (2 * Real.pi / (a * Real.sqrt (kappa ^ 2 - 1) * u)) := by
        rw [← Real.sqrt_div (by positivity : (0:ℝ) ≤ 2 * Real.pi
          / (a * Real.sqrt (kappa ^ 2 - 1)))]
        congr 1
        field_simp
      rw [hval]
      refine Real.sqrt_le_sqrt ?_
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      nlinarith [hKslope]
    have hfirst : Real.exp (-(a * HTGeometry.csqrtRe
          (xiMassSpacelikePropagationArgument sigma u h)))
        * Real.exp (2 / (a * HTGeometry.csqrtRe
          (xiMassSpacelikePropagationArgument sigma u h)))
        ≤ Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) * Real.exp (2 / (a * sigma)) :=
      mul_le_mul h1 h2 (Real.exp_nonneg _) (Real.exp_nonneg _)
    exact mul_le_mul hfirst h3 (Real.sqrt_nonneg _) (by positivity)
  have hprod1 : (0 : ℝ) ≤ 2 * a := by positivity
  have hchain : 2 * a
        * (‖(sigma : ℂ) + (u : ℂ) * I‖
          / ‖HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)‖)
        * (|h| / ‖HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)‖)
        * (a + 1 / (HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)).re)
        * (Real.exp (-(a * HTGeometry.csqrtRe
            (xiMassSpacelikePropagationArgument sigma u h)))
          * Real.exp (2 / (a * HTGeometry.csqrtRe
            (xiMassSpacelikePropagationArgument sigma u h)))
          * Real.sqrt (2 * Real.pi
              / (a * HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h))))
      ≤ 2 * a * (1 + 1 / Real.sqrt (kappa ^ 2 - 1)) * (kappa / Real.sqrt (kappa ^ 2 - 1))
        * (a + 1 / sigma)
        * (Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) * Real.exp (2 / (a * sigma))
          * (Real.sqrt (2 * Real.pi / (a * Real.sqrt (kappa ^ 2 - 1))) / Real.sqrt u)) := by
    have hA : (0 : ℝ) ≤ ‖(sigma : ℂ) + (u : ℂ) * I‖
        / ‖HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)‖ := by positivity
    have hB : (0 : ℝ) ≤ |h| / ‖HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)‖ :=
      by positivity
    have hC : (0 : ℝ) ≤ a + 1 / (HTGeometry.csqrt
        (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)).re := by
      rw [hzre]
      positivity
    have s1 := mul_le_mul_of_nonneg_left hratio1 hprod1
    have s2 := mul_le_mul s1 hratio2 hB (by positivity)
    have s3 := mul_le_mul s2 hratio3 hC (by positivity)
    exact mul_le_mul s3 hEbound hEnn (by positivity)
  refine hchain.trans (le_of_eq ?_)
  rw [xiMassBesselDerivExteriorSqrtConstant]
  ring

end

end RHTower
