import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# The midpoint rule underestimates a convex integral

For a convex integrand the value at the midpoint, times the length, is at most the integral:

```text
f((a+b)/2) · (b - a) ≤ ∫_a^b f.
```

No differentiability is needed.  Reflecting the interval about its midpoint leaves the integral
unchanged, so the integral equals the integral of the symmetrised function `(f t + f(a+b-t))/2`, and
convexity bounds that symmetrisation below by the value at the midpoint pointwise.

This is the comparison that turns a sum of midpoint values into an integral, which is how a weighted
row sum of a decreasing convex kernel is estimated.
-/

open MeasureTheory Set

namespace GaloisForLFunctions

/-- **The midpoint rule underestimates a convex integral.** -/
theorem ConvexOn.midpoint_mul_le_integral {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ConvexOn ℝ (Set.Icc a b) f) (hint : IntervalIntegrable f volume a b) :
    f ((a + b) / 2) * (b - a) ≤ ∫ t in a..b, f t := by
  have hintrefl : IntervalIntegrable (fun t => f (a + b - t)) volume a b := by
    have h := hint.comp_sub_left (a + b)
    simpa using h.symm
  -- the reflected integral is the same
  have hrefl : (∫ t in a..b, f (a + b - t)) = ∫ t in a..b, f t := by
    rw [intervalIntegral.integral_comp_sub_left f (a + b)]
    simp
  -- convexity at the midpoint of `t` and its reflection
  have hpt : ∀ t ∈ Set.Icc a b, f ((a + b) / 2) ≤ (f t + f (a + b - t)) / 2 := by
    intro t ht
    have htmem : t ∈ Set.Icc a b := ht
    have hrmem : a + b - t ∈ Set.Icc a b := by
      obtain ⟨h1, h2⟩ := ht
      exact ⟨by linarith, by linarith⟩
    have hconv := hf.2 htmem hrmem (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2)
      (by norm_num : (1:ℝ) / 2 + 1 / 2 = 1)
    have hmid : ((1:ℝ) / 2) • t + ((1:ℝ) / 2) • (a + b - t) = (a + b) / 2 := by
      show (1:ℝ) / 2 * t + (1:ℝ) / 2 * (a + b - t) = (a + b) / 2
      ring
    have hconv' : f ((a + b) / 2) ≤ 1 / 2 * f t + 1 / 2 * f (a + b - t) := by
      calc f ((a + b) / 2) = f (((1:ℝ) / 2) • t + ((1:ℝ) / 2) • (a + b - t)) := by rw [hmid]
        _ ≤ ((1:ℝ) / 2) • f t + ((1:ℝ) / 2) • f (a + b - t) := hconv
        _ = 1 / 2 * f t + 1 / 2 * f (a + b - t) := by simp only [smul_eq_mul]
    linarith
  -- integrate the pointwise bound
  have hmono : (∫ _t in a..b, f ((a + b) / 2))
      ≤ ∫ t in a..b, (f t + f (a + b - t)) / 2 := by
    refine intervalIntegral.integral_mono_on hab intervalIntegrable_const ?_ hpt
    exact (hint.add hintrefl).div_const 2
  rw [intervalIntegral.integral_const] at hmono
  have hsplit : (∫ t in a..b, (f t + f (a + b - t)) / 2) = ∫ t in a..b, f t := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add hint hintrefl, hrefl]
    ring
  rw [hsplit] at hmono
  calc f ((a + b) / 2) * (b - a) = (b - a) • f ((a + b) / 2) := by
        rw [smul_eq_mul]; ring
    _ ≤ ∫ t in a..b, f t := hmono

end GaloisForLFunctions
