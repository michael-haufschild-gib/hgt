import Mathlib

/-!
# The mean of a logarithm is at most the logarithm of the mean

Carlson's density argument bounds `∫ log|f|` on a vertical segment by the second moment of `f` on the
same segment.  The step is concavity of the logarithm, and it needs no measure-theoretic Jensen
machinery: the tangent line at the mean,

```text
log x ≤ x/c + log c − 1        (x > 0, c > 0)
```

integrates to

```text
∫_a^b log g ≤ (b − a) · log ( (∫_a^b g) / (b − a) ) ,
```

and applying it to `g = ‖f‖²` gives `2∫ log‖f‖ ≤ (b−a)·log( mean of ‖f‖² )`.  Choosing `c` to be the
mean makes the linear term cancel exactly.
-/

open MeasureTheory intervalIntegral

namespace RHTower

/-- The tangent-line bound for the logarithm at a positive point. -/
theorem log_le_div_add_log_sub_one {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    Real.log x ≤ x / c + Real.log c - 1 := by
  have hxc : 0 < x / c := div_pos hx hc
  have h := Real.log_le_sub_one_of_pos hxc
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hc)] at h
  linarith

/-- **The mean-log bound.**  For a positive integrable `g` on `[a,b]` the average of `log g` is at
most the logarithm of the average of `g`. -/
theorem integral_log_le_length_mul_log_mean {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hpos : ∀ t, 0 < g t) (hint : IntervalIntegrable g volume a b)
    (hlogint : IntervalIntegrable (fun t => Real.log (g t)) volume a b) :
    (∫ t in a..b, Real.log (g t))
      ≤ (b - a) * Real.log ((∫ t in a..b, g t) / (b - a)) := by
  have hlen : 0 < b - a := by linarith
  have hgpos : 0 < ∫ t in a..b, g t := by
    have := intervalIntegral.intervalIntegral_pos_of_pos_on hint (fun x _ => hpos x) hab
    exact this
  set c : ℝ := (∫ t in a..b, g t) / (b - a) with hc
  have hcpos : 0 < c := div_pos hgpos hlen
  have hbound : (∫ t in a..b, Real.log (g t))
      ≤ ∫ t in a..b, (g t / c + Real.log c - 1) := by
    refine intervalIntegral.integral_mono_on hab.le hlogint ?_ ?_
    · exact ((hint.div_const c).add _root_.intervalIntegrable_const).sub
        _root_.intervalIntegrable_const
    · intro t _
      exact log_le_div_add_log_sub_one (hpos t) hcpos
  have hcmul : c * (b - a) = ∫ t in a..b, g t := by
    rw [hc]; field_simp
  have hrhs : (∫ t in a..b, (g t / c + Real.log c - 1))
      = (b - a) * Real.log c := by
    rw [intervalIntegral.integral_sub
        ((hint.div_const c).add _root_.intervalIntegrable_const)
        _root_.intervalIntegrable_const,
      intervalIntegral.integral_add (hint.div_const c) _root_.intervalIntegrable_const,
      intervalIntegral.integral_div]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    rw [← hcmul]
    field_simp
    ring
  linarith [hbound, hrhs.le, hrhs.ge]

/-- **The form Carlson consumes.**  With `g = ‖f‖²` the bound reads
`2∫ log‖f‖ ≤ (b−a)·log(mean of ‖f‖²)`: a second-moment bound on a vertical segment caps the integral
of `log‖f‖` on that segment. -/
theorem two_mul_integral_log_norm_le {a b : ℝ} (hab : a < b) {f : ℝ → ℂ}
    (hpos : ∀ t, f t ≠ 0)
    (hint : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume a b)
    (hlogint : IntervalIntegrable (fun t => Real.log (‖f t‖ ^ 2)) volume a b) :
    2 * (∫ t in a..b, Real.log ‖f t‖)
      ≤ (b - a) * Real.log ((∫ t in a..b, ‖f t‖ ^ 2) / (b - a)) := by
  have hgpos : ∀ t, 0 < ‖f t‖ ^ 2 := fun t => by
    have : 0 < ‖f t‖ := norm_pos_iff.mpr (hpos t)
    positivity
  have hmain := integral_log_le_length_mul_log_mean hab hgpos hint hlogint
  have hsplit : (∫ t in a..b, Real.log (‖f t‖ ^ 2))
      = 2 * ∫ t in a..b, Real.log ‖f t‖ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hn : 0 < ‖f t‖ := norm_pos_iff.mpr (hpos t)
    rw [Real.log_pow]
    push_cast
    ring
  rw [hsplit] at hmain
  exact hmain

end RHTower
