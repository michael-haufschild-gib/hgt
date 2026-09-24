import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Two-sided size of the Gamma function on a vertical line

The Euler integral is dominated termwise by its real counterpart, so `‖Γ(s)‖ ≤ Γ(Re s)` whenever
`Re s > 0`.  The reflection formula turns this into a bound for the reciprocal:

```text
1/Γ(z) = Γ(1-z) · sin(π z) / π,      ‖1/Γ(z)‖ ≤ Γ(1 - Re z) e^{π|Im z|} / π   (Re z < 1).
```

The reciprocal Gamma function therefore grows at most like a single exponential in the height,
uniformly on every left vertical strip.  This is the size a Phragmén--Lindelöf argument for a
function with a Gamma factor in its denominator consumes.
-/

open Complex MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The Euler integral is dominated by the real one.** -/
theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, Real.Gamma_eq_integral hs]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos (-x)), Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  congr 1

/-- The sine grows at most like the exponential of the imaginary part. -/
theorem norm_sin_le_exp_abs_im (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  have hsin : Complex.sin w = (Complex.exp (-w * I) - Complex.exp (w * I)) * I / 2 := by
    rw [Complex.sin]
  have h1 : ‖Complex.exp (w * I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  have h2 : ‖Complex.exp (-w * I)‖ = Real.exp w.im := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  have htri : ‖Complex.exp (-w * I) - Complex.exp (w * I)‖ ≤ 2 * Real.exp |w.im| := by
    refine (norm_sub_le _ _).trans ?_
    rw [h1, h2]
    have hb1 : Real.exp (-w.im) ≤ Real.exp |w.im| := Real.exp_le_exp.mpr (neg_le_abs _)
    have hb2 : Real.exp w.im ≤ Real.exp |w.im| := Real.exp_le_exp.mpr (le_abs_self _)
    linarith
  rw [hsin, norm_div, norm_mul, Complex.norm_I, mul_one]
  rw [show ‖(2 : ℂ)‖ = 2 by simp, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- **The reflection formula in reciprocal form.** -/
theorem inv_Gamma_eq {z : ℂ} (hz : z.re < 1) :
    (Complex.Gamma z)⁻¹
      = Complex.Gamma (1 - z) * Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ) := by
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have href := Complex.Gamma_mul_Gamma_one_sub z
  have h1z : Complex.Gamma (1 - z) ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m hcon => ?_)
    have hc := congrArg Complex.re hcon
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at hc
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  by_cases hsin : Complex.sin ((Real.pi : ℂ) * z) = 0
  · rw [hsin, mul_zero, zero_div]
    rw [hsin, div_zero] at href
    rcases mul_eq_zero.mp href with h | h
    · rw [h, inv_zero]
    · exact absurd h h1z
  · refine inv_eq_of_mul_eq_one_right ?_
    rw [eq_div_iff hsin] at href
    field_simp
    rw [mul_comm z ((Real.pi : ℂ))]
    linear_combination href

/-- **The reciprocal Gamma function grows at most exponentially in the height.** -/
theorem norm_inv_Gamma_le {z : ℂ} (hz : z.re < 1) :
    ‖(Complex.Gamma z)⁻¹‖
      ≤ Real.Gamma (1 - z.re) * Real.exp (Real.pi * |z.im|) / Real.pi := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hΓ : ‖Complex.Gamma (1 - z)‖ ≤ Real.Gamma (1 - z.re) := by
    have h := norm_Gamma_le_Gamma_re (s := 1 - z) (by simp; linarith)
    simpa using h
  have hs : ‖Complex.sin ((Real.pi : ℂ) * z)‖ ≤ Real.exp (Real.pi * |z.im|) := by
    have h := norm_sin_le_exp_abs_im ((Real.pi : ℂ) * z)
    have him : ((Real.pi : ℂ) * z).im = Real.pi * z.im := by simp [Complex.mul_im]
    rw [him, abs_mul, abs_of_pos hπ] at h
    exact h
  rw [inv_Gamma_eq hz, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ, norm_mul]
  gcongr

end

end GaloisForLFunctions.HTGeometry
