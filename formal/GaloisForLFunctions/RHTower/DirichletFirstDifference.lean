import GaloisForLFunctions.RHTower.DirichletKernelEstimate

/-!
# The unit first difference of a power

Two sharp increment bounds over a unit step.  The real one,

```text
x^{−p} − (x+1)^{−p}  ≤  p · x^{−p−1}        (p > 0, x > 0) ,
```

is the fundamental theorem of calculus on `[x, x+1]` with the integrand `p y^{−p−1}` bounded by its
value at the left endpoint.  Feeding it into the complex increment estimate at exponent `s+1` makes
the factor `Re s + 1` cancel and leaves

```text
‖x^{−(s+1)} − (x+1)^{−(s+1)}‖  ≤  ‖s+1‖ · x^{−Re s−2} .
```

That is the derivative-scale estimate: one unit step costs one power of `x` and one factor of the
exponent.  Iterating it gives the second-difference bound that controls a doubly Abel-summed
Dirichlet series.
-/

noncomputable section

open MeasureTheory intervalIntegral

namespace GaloisForLFunctions.RHTower

/-- **The real unit first difference.** -/
theorem rpow_sub_rpow_succ_le {p : ℝ} (hp : 0 < p) {x : ℝ} (hx : 0 < x) :
    x ^ (-p) - (x + 1) ^ (-p) ≤ p * x ^ (-p - 1) := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hderiv : ∀ y ∈ Set.uIcc x (x + 1), HasDerivAt (fun u : ℝ => -(u ^ (-p)))
      (p * y ^ (-p - 1)) y := by
    intro y hy
    have hy0 : y ≠ 0 := by
      rw [Set.uIcc_of_le (by linarith)] at hy
      exact ne_of_gt (lt_of_lt_of_le hx hy.1)
    have hd := Real.hasDerivAt_rpow_const (x := y) (p := -p) (Or.inl hy0)
    have hd2 := hd.neg
    have hval : -(-p * y ^ (-p - 1)) = p * y ^ (-p - 1) := by ring
    rwa [hval] at hd2
  have hcont : ContinuousOn (fun y : ℝ => p * y ^ (-p - 1)) (Set.uIcc x (x + 1)) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := by
      rw [Set.uIcc_of_le (by linarith)] at hy
      exact lt_of_lt_of_le hx hy.1
    exact ((Real.continuousAt_rpow_const y (-p - 1) (Or.inl (ne_of_gt hy0))).const_mul
      p).continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have hval : x ^ (-p) - (x + 1) ^ (-p) = ∫ y in x..(x + 1), p * y ^ (-p - 1) := by
    rw [hftc]
    ring
  rw [hval]
  have hbound : ∀ y ∈ Set.uIoc x (x + 1), ‖p * y ^ (-p - 1)‖ ≤ p * x ^ (-p - 1) := by
    intro y hy
    rw [Set.uIoc_of_le (by linarith)] at hy
    have hy0 : (0 : ℝ) < y := lt_trans hx hy.1
    have hmono : y ^ (-p - 1) ≤ x ^ (-p - 1) :=
      Real.rpow_le_rpow_of_nonpos hx hy.1.le (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hmono hp.le
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := x + 1) hbound
  have habs : |x + 1 - x| = 1 := by
    rw [show x + 1 - x = 1 by ring, abs_one]
  rw [habs, mul_one] at hle
  exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hle)

/-- **The complex unit first difference at exponent `s+1`.**  The factor `Re s + 1` cancels between
the increment estimate and the real bound. -/
theorem norm_cpow_neg_succ_sub_succ_le {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (-(s + 1)) - ((x + 1 : ℝ) : ℂ) ^ (-(s + 1))‖ ≤ ‖s + 1‖ * x ^ (-s.re - 2) := by
  have hs1 : 0 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hstep := norm_cpow_neg_sub_le hs1 hx (by linarith : x ≤ x + 1)
  have hre : (s + 1).re = s.re + 1 := by
    rw [Complex.add_re, Complex.one_re]
  rw [hre] at hstep
  have hreal := rpow_sub_rpow_succ_le (show (0 : ℝ) < s.re + 1 by linarith) hx
  have hexp : -(s.re + 1) - 1 = -s.re - 2 := by ring
  rw [hexp] at hreal
  have hcoef : (0 : ℝ) ≤ ‖s + 1‖ / (s.re + 1) := by positivity
  refine le_trans hstep ?_
  have hmul := mul_le_mul_of_nonneg_left hreal hcoef
  refine le_trans hmul ?_
  have hne : (s.re + 1) ≠ 0 := by linarith
  have hval : ‖s + 1‖ / (s.re + 1) * ((s.re + 1) * x ^ (-s.re - 2))
      = ‖s + 1‖ * x ^ (-s.re - 2) := by
    field_simp
  rw [hval]

end GaloisForLFunctions.RHTower

end
