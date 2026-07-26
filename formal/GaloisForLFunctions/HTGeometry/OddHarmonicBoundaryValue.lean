import GaloisForLFunctions.HTGeometry.SectorPowerMassLower
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Real.Sign

/-!
# The boundary value of the odd power series

At a unit-circle point `w = e^{iθ}` with `sin θ ≠ 0`, both `1 + w` and `1 - w` lie in the open right
half-plane: their real parts are `1 + cos θ` and `1 - cos θ`, and `sin θ ≠ 0` forces `|cos θ| < 1`.
The principal argument is then an arctangent, and the two arctangents are reciprocal:

```
Im (1 + w) / Re (1 + w) = sin θ / (1 + cos θ),
Im (1 - w) / Re (1 - w) = -sin θ / (1 - cos θ) = -(sin θ / (1 + cos θ))⁻¹,
```

because `1 - cos²θ = sin²θ`.  Hence `arctan x + arctan x⁻¹ = ±π/2` gives

```
Im ((log (1 + w) - log (1 - w)) / 2) = (π/4) · sgn (sin θ).
```

This is the value the odd harmonic Fourier series takes, once Abel's limit theorem identifies the
boundary series with the radial limit of the interior closed form
`GaloisForLFunctions.HTGeometry.hasSum_oddPow_div`.
-/

open Complex Real

namespace GaloisForLFunctions.HTGeometry

variable {θ : ℝ}

theorem exp_mul_I_eq (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem abs_cos_lt_one (hθ : Real.sin θ ≠ 0) : |Real.cos θ| < 1 := by
  have hpy := Real.sin_sq_add_cos_sq θ
  have hs : 0 < Real.sin θ ^ 2 := by positivity
  have : Real.cos θ ^ 2 < 1 := by nlinarith
  nlinarith [abs_nonneg (Real.cos θ), sq_abs (Real.cos θ)]

theorem re_one_add_exp_pos (hθ : Real.sin θ ≠ 0) :
    0 < (1 + Complex.exp ((θ : ℂ) * Complex.I)).re := by
  rw [exp_mul_I_eq]
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]
  have := abs_cos_lt_one hθ
  have := neg_abs_le (Real.cos θ)
  linarith

theorem re_one_sub_exp_pos (hθ : Real.sin θ ≠ 0) :
    0 < (1 - Complex.exp ((θ : ℂ) * Complex.I)).re := by
  rw [exp_mul_I_eq]
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]
  have := abs_cos_lt_one hθ
  have := le_abs_self (Real.cos θ)
  linarith

/-- The two half-plane slopes are reciprocal. -/
theorem slope_reciprocal (hθ : Real.sin θ ≠ 0) :
    -Real.sin θ / (1 - Real.cos θ) = -(Real.sin θ / (1 + Real.cos θ))⁻¹ := by
  have hpy := Real.sin_sq_add_cos_sq θ
  have habs := abs_cos_lt_one hθ
  have h1 : 0 < 1 + Real.cos θ := by
    have := neg_abs_le (Real.cos θ); linarith
  have h2 : 0 < 1 - Real.cos θ := by
    have := le_abs_self (Real.cos θ); linarith
  rw [inv_div]
  field_simp
  nlinarith [hpy]

/-- **The boundary value.**  The imaginary part of the half log-ratio is the square wave. -/
theorem im_half_log_ratio (hθ : Real.sin θ ≠ 0) :
    ((Complex.log (1 + Complex.exp ((θ : ℂ) * Complex.I))
        - Complex.log (1 - Complex.exp ((θ : ℂ) * Complex.I))) / 2).im
      = π / 4 * Real.sign (Real.sin θ) := by
  have hpy := Real.sin_sq_add_cos_sq θ
  have habs := abs_cos_lt_one hθ
  have h1 : 0 < 1 + Real.cos θ := by
    have := neg_abs_le (Real.cos θ); linarith
  have hadd := re_one_add_exp_pos hθ
  have hsub := re_one_sub_exp_pos hθ
  have hreAdd : (1 + Complex.exp ((θ : ℂ) * Complex.I)).re = 1 + Real.cos θ := by
    rw [exp_mul_I_eq]; simp [Complex.cos_ofReal_re]
  have himAdd : (1 + Complex.exp ((θ : ℂ) * Complex.I)).im = Real.sin θ := by
    rw [exp_mul_I_eq]; simp [Complex.sin_ofReal_re]
  have hreSub : (1 - Complex.exp ((θ : ℂ) * Complex.I)).re = 1 - Real.cos θ := by
    rw [exp_mul_I_eq]; simp [Complex.cos_ofReal_re]
  have himSub : (1 - Complex.exp ((θ : ℂ) * Complex.I)).im = -Real.sin θ := by
    rw [exp_mul_I_eq]; simp [Complex.sin_ofReal_re]
  have hargAdd : (Complex.log (1 + Complex.exp ((θ : ℂ) * Complex.I))).im
      = Real.arctan (Real.sin θ / (1 + Real.cos θ)) := by
    rw [Complex.log_im, complexArg_eq_arctan_of_re_pos hadd, hreAdd, himAdd]
  have hargSub : (Complex.log (1 - Complex.exp ((θ : ℂ) * Complex.I))).im
      = Real.arctan (-(Real.sin θ / (1 + Real.cos θ))⁻¹) := by
    rw [Complex.log_im, complexArg_eq_arctan_of_re_pos hsub, hreSub, himSub,
      slope_reciprocal hθ]
  set x : ℝ := Real.sin θ / (1 + Real.cos θ) with hx
  have hdiv : ((Complex.log (1 + Complex.exp ((θ : ℂ) * Complex.I))
      - Complex.log (1 - Complex.exp ((θ : ℂ) * Complex.I))) / 2).im
      = (Real.arctan x - Real.arctan (-x⁻¹)) / 2 := by
    simp only [Complex.div_im, Complex.sub_im, hargAdd, hargSub]
    norm_num
    ring
  rw [hdiv, Real.arctan_neg]
  rcases lt_trichotomy (Real.sin θ) 0 with hs | hs | hs
  · have hxneg : x < 0 := div_neg_of_neg_of_pos hs h1
    rw [Real.arctan_inv_of_neg hxneg, Real.sign_of_neg hs]
    ring
  · exact absurd hs hθ
  · have hxpos : 0 < x := div_pos hs h1
    rw [Real.arctan_inv_of_pos hxpos, Real.sign_of_pos hs]
    ring

end GaloisForLFunctions.HTGeometry
