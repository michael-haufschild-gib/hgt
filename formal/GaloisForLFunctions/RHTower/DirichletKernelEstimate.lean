import Mathlib

/-!
# The Dirichlet kernel increment estimate

The analytic core of every convergence theorem for ordinary Dirichlet series: for `Re s > 0` and
`0 < a ≤ b`,

```text
‖a^{−s} − b^{−s}‖  ≤  (‖s‖ / Re s) · (a^{−Re s} − b^{−Re s}) .
```

The proof is the fundamental theorem of calculus on `[a,b]` for `x ↦ x^{−s}`, whose derivative has
norm `‖s‖ x^{−Re s − 1}`; integrating that bound reproduces the real increment divided by `Re s`.

This is the estimate that makes Abel summation work: it converts a bound on the partial sums of the
coefficients into convergence of the series throughout the open half-plane to the right, and it is
the only place where the complex exponent interacts with the real one.
-/

noncomputable section

open MeasureTheory intervalIntegral

namespace GaloisForLFunctions.RHTower

/-- **The Dirichlet kernel increment estimate.** -/
theorem norm_cpow_neg_sub_le {s : ℂ} (hs : 0 < s.re) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖
      ≤ (‖s‖ / s.re) * (a ^ (-s.re) - b ^ (-s.re)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hsne : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hs1 : -s - 1 ≠ 0 := by
    intro h
    have hval : s = -1 := by linear_combination -h
    rw [hval] at hs
    norm_num at hs
  have hpos : ∀ x ∈ Set.uIcc a b, (0 : ℝ) < x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact lt_of_lt_of_le ha hx.1
  -- the derivative on the interval
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x := by
    intro x hx
    exact hasDerivAt_ofReal_cpow_const (ne_of_gt (hpos x hx)) (neg_ne_zero.2 hsne)
  have hcont : ContinuousOn (fun x : ℝ => -s * (x : ℂ) ^ (-s - 1)) (Set.uIcc a b) := by
    intro x hx
    have hd := hasDerivAt_ofReal_cpow_const (r := -s - 1) (ne_of_gt (hpos x hx)) hs1
    exact ((hd.continuousAt).const_mul (-s)).continuousWithinAt
  have hint : IntervalIntegrable (fun x : ℝ => -s * (x : ℂ) ^ (-s - 1)) volume a b :=
    hcont.intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- rewrite the increment as an integral
  have hkey : (a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)
      = ∫ x in a..b, s * (x : ℂ) ^ (-s - 1) := by
    have hneg : (∫ x in a..b, s * (x : ℂ) ^ (-s - 1))
        = -∫ x in a..b, -s * (x : ℂ) ^ (-s - 1) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun x _ => ?_
      ring
    rw [hneg, hftc]
    ring
  rw [hkey]
  -- bound the integral by the integral of the norm
  refine (intervalIntegral.norm_integral_le_integral_norm hab).trans ?_
  have hnorm : ∀ x ∈ Set.uIcc a b, ‖s * (x : ℂ) ^ (-s - 1)‖ = ‖s‖ * x ^ (-s.re - 1) := by
    intro x hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hpos x hx)]
    congr 2
    simp
  rw [intervalIntegral.integral_congr hnorm, intervalIntegral.integral_const_mul]
  have hzero : (0 : ℝ) ∉ Set.uIcc a b := by
    intro h
    exact absurd (hpos 0 h) (lt_irrefl 0)
  rw [integral_rpow (Or.inr ⟨by intro h; simp at h; linarith, hzero⟩)]
  have hexp : -s.re - 1 + 1 = -s.re := by ring
  rw [hexp]
  have hsre : s.re ≠ 0 := ne_of_gt hs
  field_simp

end GaloisForLFunctions.RHTower

end
