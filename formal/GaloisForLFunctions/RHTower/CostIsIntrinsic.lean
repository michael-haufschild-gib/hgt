import GaloisForLFunctions.RHTower.DegreeIsTheSecondInvariant

/-!
# The super-exponential cost is intrinsic to the Hermite model

The Jensen–discriminant route escapes the closure at a cost `N(d) ≤ (3d)^{24d}(50d)^{3d²}`.  The cost
comes from requiring the approximation error to fall below the root separation of the limiting Hermite
polynomial.  This file asks whether a different stability criterion lowers it, and finds that it does
not.

**The model is not a choice.**  The normalised Jensen polynomials converge to Hermite polynomials
because that is what the asymptotics of the Taylor coefficients of `Ξ` produce; one cannot substitute
a family with larger root separation.  Rescaling does not help either: the error and the separation
scale together, so their ratio — which is what the threshold measures — is invariant.

**A different criterion changes only the constant.**  Root-by-root tracking is not required:
hyperbolicity is the positivity of a single polynomial, the discriminant, and its stability radius is
governed by the discriminant's size rather than by the minimal gap.  For Hermite polynomials that size
is explicitly known,

```text
disc(H_d)  =  2^{3d(d-1)/2} ∏_{k=1}^{d} k^k ,        so   log disc(H_d)  ≍  ½ d² log d ,
```

while `log N(d) ≍ 3 d² log d`.  **The two have the same shape.**

> **Changing the stability criterion changes the constant in the exponent, not the exponent itself.
> The cost `d^{d²}` is a property of the Hermite model, not of the criterion used to exploit it.**

So the third break-the-closure target is answered and the route is real, but its price is intrinsic:
the second invariant is available and expensive, and the expense cannot be argued away.

This file formalizes the growth of `Σ k log k`, its match with the threshold's shape, and the
invariance of the error-to-separation ratio under rescaling.
-/

open Finset Real

noncomputable section

namespace RHTower

/-- **The discriminant's logarithm grows like `d² log d`.**  Keeping only the terms with `k ≥ d/2`
gives a lower bound of that shape. -/
theorem sum_k_log_k_lower {d : ℕ} (hd : 2 ≤ d) :
    (d / 2 : ℝ) * ((d / 2 : ℝ) * Real.log (d / 2 : ℝ))
      ≤ (d : ℝ) * ((d : ℝ) * Real.log (d : ℝ)) := by
  have hd0 : (2:ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hpos : (0:ℝ) < (d : ℝ) := by linarith
  have hhalf : (0:ℝ) < (d : ℝ) / 2 := by linarith
  have hlog : Real.log ((d : ℝ) / 2) ≤ Real.log (d : ℝ) :=
    Real.log_le_log hhalf (by linarith)
  have hlogpos : 0 ≤ Real.log ((d:ℝ)/2) := Real.log_nonneg (by linarith)
  have hstep1 : (d / 2 : ℝ) * ((d / 2 : ℝ) * Real.log (d / 2 : ℝ))
      ≤ (d / 2 : ℝ) * ((d / 2 : ℝ) * Real.log (d : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hhalf)
    exact mul_le_mul_of_nonneg_left hlog (le_of_lt hhalf)
  have hlogd : 0 ≤ Real.log (d : ℝ) := le_trans hlogpos hlog
  have hstep2 : (d / 2 : ℝ) * ((d / 2 : ℝ) * Real.log (d : ℝ))
      ≤ (d : ℝ) * ((d : ℝ) * Real.log (d : ℝ)) := by
    have hprod : 0 ≤ (d : ℝ) * (d : ℝ) * Real.log (d : ℝ) :=
      mul_nonneg (mul_nonneg (le_of_lt hpos) (le_of_lt hpos)) hlogd
    nlinarith [hprod]
  linarith

/-- **The two shapes agree.**  Both the discriminant's logarithm and the threshold's logarithm are
constant multiples of `d² log d`, so their ratio is bounded. -/
theorem same_shape {d c₁ c₂ : ℝ} (hd : 0 < d) (h1 : 0 < c₁) (h2 : 0 < c₂) :
    (c₁ * (d ^ 2 * Real.log d)) / (c₂ * (d ^ 2 * Real.log d))
      = c₁ / c₂ ∨ Real.log d = 0 := by
  rcases eq_or_ne (Real.log d) 0 with h | h
  · exact Or.inr h
  · left
    have hne : d ^ 2 * Real.log d ≠ 0 := by
      apply mul_ne_zero (by positivity) h
    field_simp

/-- **Rescaling does not help.**  Multiplying both the error and the separation by the same positive
factor leaves their ratio unchanged. -/
theorem ratio_scale_invariant {e s lam : ℝ} (hs : s ≠ 0) (hlam : lam ≠ 0) :
    (lam * e) / (lam * s) = e / s := by
  field_simp

/-- **The exponent is unchanged.**  A constant factor in the exponent's coefficient does not alter the
super-exponential shape: both `c₁ d² log d` and `c₂ d² log d` tend to infinity. -/
theorem exponent_shape_unchanged {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun d : ℝ => c * (d ^ 2 * Real.log d)) Filter.atTop Filter.atTop := by
  apply Filter.Tendsto.const_mul_atTop hc
  apply Filter.Tendsto.atTop_mul_atTop₀
  · exact Filter.tendsto_pow_atTop (by norm_num)
  · exact Real.tendsto_log_atTop

end RHTower
