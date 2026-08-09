import Mathlib

/-!
# One more power beats a logarithm

A polynomial of degree `q` times the logarithm of a polynomial is eventually smaller than any
positive multiple of the next power.  This is the comparison a rarity exponent of order
`n^q log n` loses to a ramp exponent of order `n^{q+1}`.

The statement is uniform in the constants: the leading coefficient of the winning side may be
arbitrarily small and the losing side arbitrarily large.
-/

open Filter

namespace HTGeometry

/-- **A logarithm cannot survive one more power.**  Eventually `a x` dominates
`b log d + b q log x`, whatever the constants, as long as `a` is positive. -/
theorem eventually_logAffine_lt_linear {a b d : ℝ} (ha : 0 < a) (q : ℕ) :
    ∀ᶠ x : ℝ in atTop, b * Real.log d + b * (q : ℝ) * Real.log x < a * x := by
  have hlittle : (fun x : ℝ => b * (q : ℝ) * Real.log x) =o[atTop] (fun x : ℝ => x) :=
    (Real.isLittleO_log_id_atTop.const_mul_left (b * (q : ℝ)))
  have hbound := hlittle.bound (c := a / 2) (by positivity)
  have hconst : ∀ᶠ x : ℝ in atTop, b * Real.log d < a / 2 * x := by
    have : Filter.Tendsto (fun x : ℝ => a / 2 * x) atTop atTop :=
      Filter.tendsto_id.const_mul_atTop (by positivity)
    exact this.eventually_gt_atTop _
  filter_upwards [hbound, hconst, eventually_gt_atTop (0 : ℝ)] with x hx hxc hx0
  have h1 : b * (q : ℝ) * Real.log x ≤ a / 2 * x := by
    have := hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0] at this
    calc b * (q : ℝ) * Real.log x ≤ |b * (q : ℝ) * Real.log x| := le_abs_self _
      _ ≤ a / 2 * x := this
  linarith

/-- **One more power beats a polynomial logarithm.**  For every positive leading coefficient `a`
and every constants `b, d`, the quantity `b x^q log (d x^q)` is eventually below `a x^{q+1}`. -/
theorem eventually_polyLog_lt_pow_succ (q : ℕ) {a b d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    ∀ᶠ x : ℝ in atTop,
      b * x ^ q * Real.log (d * x ^ q) < a * x ^ (q + 1) := by
  filter_upwards [eventually_logAffine_lt_linear (b := b) (d := d) ha q,
    eventually_gt_atTop (0 : ℝ)]
    with x hx hx0
  have hxq : (0 : ℝ) < x ^ q := by positivity
  have hlog : Real.log (d * x ^ q) = Real.log d + (q : ℝ) * Real.log x := by
    rw [Real.log_mul (ne_of_gt hd) (ne_of_gt hxq), Real.log_pow]
  rw [hlog, pow_succ]
  calc b * x ^ q * (Real.log d + (q : ℝ) * Real.log x)
      = x ^ q * (b * Real.log d + b * (q : ℝ) * Real.log x) := by ring
    _ < x ^ q * (a * x) := by
        exact mul_lt_mul_of_pos_left hx hxq
    _ = a * (x ^ q * x) := by ring

/-- The natural-number form. -/
theorem eventually_polyLog_lt_pow_succ_nat (q : ℕ) {a b d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      b * (n : ℝ) ^ q * Real.log (d * (n : ℝ) ^ q) < a * (n : ℝ) ^ (q + 1) :=
  tendsto_natCast_atTop_atTop.eventually (eventually_polyLog_lt_pow_succ q ha hd)

end HTGeometry
