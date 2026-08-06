import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# The logarithmic Gamma integral at one

The derivative of the Gamma integral at `s = 1` is the logarithmic moment of the exponential
density, and Euler's constant is its negative:

```text
∫₀^∞ (log t) e^(-t) dt = Γ'(1) = -γ.
```

This is the analytic constant that converts Mertens' second theorem into Mertens' third theorem.
-/

open MeasureTheory Set Filter Topology

namespace HTGeometry

noncomputable section

/-- **The logarithmic moment of the exponential density is `-γ`.** -/
theorem integral_log_mul_exp_neg_Ioi :
    (∫ t in Ioi (0 : ℝ), Real.log t * Real.exp (-t)) = -Real.eulerMascheroniConstant := by
  have hone : (0 : ℝ) < (1 : ℂ).re := by norm_num
  have hd := Complex.hasDerivAt_GammaIntegral hone
  have hcong : (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ ((1 : ℂ) - 1) * ((Real.log t : ℂ) * (Real.exp (-t) : ℂ))) =
      ((∫ t in Ioi (0 : ℝ), Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [sub_self, Complex.cpow_zero, one_mul, Complex.ofReal_mul]
  rw [hcong] at hd
  have hGamma : HasDerivAt Complex.Gamma
      (((∫ t in Ioi (0 : ℝ), Real.log t * Real.exp (-t) : ℝ) : ℂ)) 1 := by
    refine hd.congr_of_eventuallyEq ?_
    have hopen : IsOpen {s : ℂ | 0 < s.re} :=
      Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
    filter_upwards [hopen.mem_nhds hone] with s hs
    exact Complex.Gamma_eq_integral hs
  have hreal : HasDerivAt (fun x : ℝ => (Complex.Gamma (x : ℂ)).re)
      (((∫ t in Ioi (0 : ℝ), Real.log t * Real.exp (-t) : ℝ) : ℂ)).re (1 : ℝ) := by
    simpa using hGamma.real_of_complex
  have hfun : (fun x : ℝ => (Complex.Gamma (x : ℂ)).re) = Real.Gamma := by
    funext x
    rw [Complex.Gamma_ofReal, Complex.ofReal_re]
  rw [hfun, Complex.ofReal_re] at hreal
  have hderiv : deriv Real.Gamma 1 = ∫ t in Ioi (0 : ℝ), Real.log t * Real.exp (-t) :=
    hreal.deriv
  rw [Real.eulerMascheroniConstant_eq_neg_deriv, hderiv, neg_neg]

end

end HTGeometry
