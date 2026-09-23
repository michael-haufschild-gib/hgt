import GaloisForLFunctions.RHTower.XiWardCubicApertureRateChangeDefectLaw

/-!
# Cubic Ward aperture rate-change connection jet (W-H196)

W-H195 identifies the exact finite-aperture work forced on every landing which changes one
generalized radial mode into another.  This module extracts its infinitesimal invariant.

For a landing

`r * exp (-z r) ↦ r * exp (-w r)`, 

the covariance defect, divided by `c²`, converges at the punctured radial boundary to
`2 (w - z)`.  Thus the first non-flat aperture connection must carry the complete complex
spectral displacement: its real part is the horizontal decay-rate change and its imaginary part
is the signed ordinate change.  No modulus-only or unsigned-energy correction can supply this
jet.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Derivative of one complex radial exponential along the real aperture. -/
theorem hasDerivAt_exp_neg_complex_mul (z : ℂ) (c : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (-(z * (x : ℂ))))
      (Complex.exp (-(z * (c : ℂ))) * (-z)) c := by
  have hlin : HasDerivAt (fun x : ℝ => -(z * (x : ℂ))) (-z) c := by
    have h := ((Complex.hasDerivAt_ofReal c).const_mul z).neg
    have hfun : -(fun x : ℝ => z * (x : ℂ)) =
        (fun x : ℝ => -(z * (x : ℂ))) := by rfl
    rw [← hfun]
    simpa only [mul_one] using h
  exact hlin.cexp

/-- First divided difference of two radial characters retains their signed complex gap. -/
theorem tendsto_exp_neg_mul_difference_div_aperture
    (z w : ℂ) :
    Tendsto (fun c : ℝ =>
      (Complex.exp (-(z * (c : ℂ))) -
        Complex.exp (-(w * (c : ℂ)))) / (c : ℂ))
      (nhdsWithin 0 ({0}ᶜ)) (nhds (w - z)) := by
  have hz := hasDerivAt_exp_neg_complex_mul z 0
  have hw := hasDerivAt_exp_neg_complex_mul w 0
  have hd := hz.sub hw
  simp only [ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
    one_mul] at hd
  rw [hasDerivAt_iff_tendsto_slope] at hd
  convert hd using 1
  · funext c
    simp [slope, Complex.real_smul, div_eq_mul_inv]
    ring
  · ring

/-- Exact infinitesimal connection invariant forced by every rate-changing landing. -/
theorem tendsto_apertureCovarianceDefect_div_sq
    (T : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ)) (z w : ℂ)
    (hland : T (xiWardCubicRadialGeneralizedMode z) =
      xiWardCubicRadialGeneralizedMode w) :
    Tendsto (fun c : ℝ =>
      xiWardCubicApertureCovarianceDefect T c
          (Complex.exp (-(z * (c : ℂ))))
          (xiWardCubicRadialGeneralizedMode z) 0 / (c : ℂ) ^ (2 : ℕ))
      (nhdsWithin 0 ({0}ᶜ)) (nhds (2 * (w - z))) := by
  have hdiff := tendsto_exp_neg_mul_difference_div_aperture z w
  have hexp : Tendsto (fun c : ℝ => Complex.exp (-(w * (c : ℂ))))
      (nhdsWithin 0 ({0}ᶜ)) (nhds 1) := by
    have hcont : ContinuousAt (fun c : ℝ =>
        Complex.exp (-(w * (c : ℂ)))) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun c : ℝ =>
      (2 : ℂ) * (Complex.exp (-(w * (c : ℂ))) *
        ((Complex.exp (-(z * (c : ℂ))) -
          Complex.exp (-(w * (c : ℂ)))) / (c : ℂ))))
      (nhdsWithin 0 ({0}ᶜ)) (nhds (2 * (w - z))) := by
    simpa only [one_mul] using
      (tendsto_const_nhds.mul (hexp.mul hdiff))
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  rw [xiWardCubicApertureCovarianceDefect_mode_landing_apply_zero
    T z w c hland]
  have hcC : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc
  field_simp [hcC]

end

end RHTower
