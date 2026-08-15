import GaloisForLFunctions.RHTower.XiWardCubicApertureIntertwiningRateNoGo

/-!
# Cubic Ward aperture rate-change defect law (W-H195)

W-H194 proves that the completed landing cannot intertwine aperture translations.  This module
extracts the strongest positive survivor: every rate-changing landing carries one forced,
explicit second-order covariance defect.

If a linear map sends `r * exp (-z r)` to `r * exp (-w r)`, its failure to commute with the
source annihilator at aperture `c` has boundary value

`2 c exp (-w c) (exp (-z c) - exp (-w c))`.

Its squared charge is therefore an explicit positive number whenever the real decay rates differ.
This identifies the exact boundary work which a polar--Gamma colligation must retain and pay; the
nonstationarity required by W-H194 is not qualitative bookkeeping.
-/

open Complex

namespace RHTower

noncomputable section

/-- Failure of a linear landing to intertwine one second-order aperture annihilator. -/
def xiWardCubicApertureCovarianceDefect
    (T : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ)) (c : ℝ) (mu : ℂ)
    (f : ℝ → ℂ) : ℝ → ℂ :=
  T (xiWardCubicRadialSecondDifference c mu f) -
    xiWardCubicRadialSecondDifference c mu (T f)

/-- Exact wrong-character boundary value of the second translation difference. -/
theorem xiWardCubicRadialSecondDifference_mode_apply_zero_eq
    (w : ℂ) (c : ℝ) (mu : ℂ) :
    xiWardCubicRadialSecondDifference c mu
        (xiWardCubicRadialGeneralizedMode w) 0 =
      2 * (c : ℂ) * Complex.exp (-(w * (c : ℂ))) *
        (Complex.exp (-(w * (c : ℂ))) - mu) := by
  rw [xiWardCubicRadialSecondDifference, xiWardCubicRadialGeneralizedMode,
    xiWardCubicRadialGeneralizedMode, xiWardCubicRadialGeneralizedMode]
  simp only [ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, zero_mul,
    zero_add]
  have he : Complex.exp (-(w * (((2 * c : ℝ) : ℂ)))) =
      Complex.exp (-(w * (c : ℂ))) ^ 2 := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  push_cast
  ring

/-- Exact forced covariance defect of any prescribed rate-changing landing. -/
theorem xiWardCubicApertureCovarianceDefect_mode_landing_apply_zero
    (T : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ)) (z w : ℂ) (c : ℝ)
    (hland : T (xiWardCubicRadialGeneralizedMode z) =
      xiWardCubicRadialGeneralizedMode w) :
    xiWardCubicApertureCovarianceDefect T c
        (Complex.exp (-(z * (c : ℂ))))
        (xiWardCubicRadialGeneralizedMode z) 0 =
      2 * (c : ℂ) * Complex.exp (-(w * (c : ℂ))) *
        (Complex.exp (-(z * (c : ℂ))) -
          Complex.exp (-(w * (c : ℂ)))) := by
  rw [xiWardCubicApertureCovarianceDefect,
    xiWardCubicRadialSecondDifference_mode, map_zero]
  simp only [Pi.zero_apply, Pi.sub_apply, zero_sub]
  rw [hland, xiWardCubicRadialSecondDifference_mode_apply_zero_eq]
  ring

/-- Distinct real rates force nonzero boundary work at every positive aperture. -/
theorem xiWardCubicApertureCovarianceDefect_mode_landing_apply_zero_ne_zero
    (T : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ)) {z w : ℂ} {c : ℝ}
    (hc : 0 < c) (hre : z.re ≠ w.re)
    (hland : T (xiWardCubicRadialGeneralizedMode z) =
      xiWardCubicRadialGeneralizedMode w) :
    xiWardCubicApertureCovarianceDefect T c
        (Complex.exp (-(z * (c : ℂ))))
        (xiWardCubicRadialGeneralizedMode z) 0 ≠ 0 := by
  rw [xiWardCubicApertureCovarianceDefect_mode_landing_apply_zero T z w c hland]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr hc.ne'))
      (Complex.exp_ne_zero _))
    (sub_ne_zero.mpr (exp_neg_mul_ne_of_re_ne hc hre))

/-- Exact positive squared charge of the forced aperture-covariance defect. -/
theorem xiWardCubicApertureCovarianceDefect_mode_landing_normSq
    (T : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ)) (z w : ℂ) (c : ℝ)
    (hland : T (xiWardCubicRadialGeneralizedMode z) =
      xiWardCubicRadialGeneralizedMode w) :
    Complex.normSq
        (xiWardCubicApertureCovarianceDefect T c
          (Complex.exp (-(z * (c : ℂ))))
          (xiWardCubicRadialGeneralizedMode z) 0) =
      4 * c ^ 2 * Real.exp (-2 * w.re * c) *
        Complex.normSq
          (Complex.exp (-(z * (c : ℂ))) -
            Complex.exp (-(w * (c : ℂ)))) := by
  rw [xiWardCubicApertureCovarianceDefect_mode_landing_apply_zero T z w c hland]
  rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul]
  have hexp : Complex.normSq (Complex.exp (-(w * (c : ℂ)))) =
      Real.exp (-2 * w.re * c) := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  have htwo : Complex.normSq (2 : ℂ) = 4 := by
    norm_num [Complex.normSq_apply]
  have hcSq : Complex.normSq (c : ℂ) = c ^ 2 := by
    rw [Complex.normSq_ofReal]
    ring
  rw [htwo, hcSq]

end

end RHTower
