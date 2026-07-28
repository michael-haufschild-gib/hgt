import Mathlib

/-!
# The horizontal derivative of the log modulus

Littlewood's lemma is usually formalized through a continuous branch of `log f` along the boundary of
a rectangle, which is the expensive part.  It can be avoided: only the **real part** of the
logarithmic derivative is needed, and that is the derivative of `log‖f‖` along a horizontal segment.

```text
d/dσ log‖f(σ + it)‖ = Re ( f′(σ+it) / f(σ+it) ) ,
```

so by the fundamental theorem of calculus

```text
∫_{σ₀}^{σ₁} Re ( f′/f )(σ + it) dσ  =  log‖f(σ₁+it)‖ − log‖f(σ₀+it)‖ ,
```

with no branch anywhere.  Combined with the layer-cake identity this is what turns the argument
principle into Littlewood's lemma.
-/

open Complex

namespace RHTower

/-- **The log modulus differentiates to the real part of the logarithmic derivative.**  For a
path `g` through a point where `g` does not vanish, `log‖g‖` is differentiable with derivative
`Re (g′/g)`. -/
theorem hasDerivAt_log_norm_comp {g : ℝ → ℂ} {g' : ℂ} {u : ℝ}
    (hg : HasDerivAt g g' u) (hne : g u ≠ 0) :
    HasDerivAt (fun v => Real.log ‖g v‖) ((g' / g u).re) u := by
  have hre : HasDerivAt (fun v => (g v).re) g'.re u :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hg
  have him : HasDerivAt (fun v => (g v).im) g'.im u :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt u hg
  have hns : HasDerivAt (fun v => Complex.normSq (g v))
      (2 * ((g u).re * g'.re) + 2 * ((g u).im * g'.im)) u := by
    have h := (hre.mul hre).add (him.mul him)
    have hfun : (fun v => Complex.normSq (g v))
        = ((fun v => (g v).re) * fun v => (g v).re)
          + ((fun v => (g v).im) * fun v => (g v).im) := by
      funext v; simp [Complex.normSq_apply]
    rw [hfun]
    convert h using 1
    ring
  have hnspos : Complex.normSq (g u) ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hne
  have hlog : HasDerivAt (fun v => Real.log (Complex.normSq (g v)))
      ((Complex.normSq (g u))⁻¹ * (2 * ((g u).re * g'.re) + 2 * ((g u).im * g'.im))) u := by
    simpa [Function.comp] using (Real.hasDerivAt_log hnspos).comp u hns
  have hhalf := hlog.const_mul (1 / 2 : ℝ)
  have hfun2 : (fun v => (1 / 2 : ℝ) * Real.log (Complex.normSq (g v)))
      = fun v => Real.log ‖g v‖ := by
    funext v
    rw [Complex.normSq_eq_norm_sq, Real.log_pow]
    push_cast
    ring
  rw [hfun2] at hhalf
  convert hhalf using 1
  rw [Complex.div_re]
  field_simp

/-- **The horizontal log-modulus identity.**  Along a horizontal segment on which `f` does not
vanish, the integral of the real part of the logarithmic derivative is the increment of `log‖f‖`.
No branch of the logarithm is used. -/
theorem integral_re_logDeriv_horizontal {f : ℂ → ℂ} {t σ₀ σ₁ : ℝ}
    (hd : ∀ σ ∈ Set.uIcc σ₀ σ₁, HasDerivAt f (deriv f ((σ : ℂ) + t * I)) ((σ : ℂ) + t * I))
    (hne : ∀ σ ∈ Set.uIcc σ₀ σ₁, f ((σ : ℂ) + t * I) ≠ 0)
    (hint : IntervalIntegrable
      (fun σ => (deriv f ((σ : ℂ) + t * I) / f ((σ : ℂ) + t * I)).re) MeasureTheory.volume σ₀ σ₁) :
    (∫ σ in σ₀..σ₁, (deriv f ((σ : ℂ) + t * I) / f ((σ : ℂ) + t * I)).re)
      = Real.log ‖f ((σ₁ : ℂ) + t * I)‖ - Real.log ‖f ((σ₀ : ℂ) + t * I)‖ := by
  have hpath : ∀ σ : ℝ, HasDerivAt (fun v : ℝ => ((v : ℂ) + t * I)) 1 σ := by
    intro σ
    simpa using (Complex.ofRealCLM.hasDerivAt (x := σ)).add_const ((t : ℂ) * I)
  have hderiv : ∀ σ ∈ Set.uIcc σ₀ σ₁,
      HasDerivAt (fun v : ℝ => Real.log ‖f ((v : ℂ) + t * I)‖)
        ((deriv f ((σ : ℂ) + t * I) / f ((σ : ℂ) + t * I)).re) σ := by
    intro σ hσmem
    have hcomp : HasDerivAt (fun v : ℝ => f ((v : ℂ) + t * I))
        (deriv f ((σ : ℂ) + t * I)) σ := by
      simpa using (hd σ hσmem).comp σ (hpath σ)
    exact hasDerivAt_log_norm_comp hcomp (hne σ hσmem)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

end RHTower
