import Mathlib

/-!
# The right edge: a log-modulus lower bound from closeness to one

On the right edge of Carlson's rectangle the mollified function `ζ·M_y` is close to `1`, because the
mollified Dirichlet series has no terms below the cutoff and the remaining ones are small in the
half-plane of absolute convergence.  Closeness to `1` gives a pointwise lower bound on the modulus,
and hence a linear lower bound on `∫ log‖·‖` along the edge:

```text
‖w − 1‖ ≤ 1/2  ⟹  1/2 ≤ ‖w‖ ,          (T₂ − T₁)·log c ≤ ∫_{T₁}^{T₂} log‖g‖   when c ≤ ‖g‖ .
```

This is the input `hright` of `CarlsonSkeleton.count_le_of_rectangle_and_moment`, with `D = log 2`.
-/

open MeasureTheory intervalIntegral

namespace RHTower

/-- Closeness to `1` bounds the modulus below. -/
theorem half_le_norm_of_dist_le_half {w : ℂ} (h : ‖w - 1‖ ≤ 1 / 2) : (1 : ℝ) / 2 ≤ ‖w‖ := by
  have htri : ‖(1 : ℂ)‖ - ‖w‖ ≤ ‖(1 : ℂ) - w‖ := norm_sub_norm_le _ _
  rw [← norm_neg (1 - w), neg_sub] at htri
  rw [norm_one] at htri
  linarith

/-- **A pointwise modulus bound gives a linear log-modulus bound.**  If `‖g‖ ≥ c > 0` on the segment
then `∫ log‖g‖` is at least `(T₂ − T₁)·log c`. -/
theorem length_mul_log_le_integral_log_norm {T₁ T₂ c : ℝ} {g : ℝ → ℂ}
    (hT : T₁ ≤ T₂) (hc : 0 < c) (hlow : ∀ t ∈ Set.uIcc T₁ T₂, c ≤ ‖g t‖)
    (hint : IntervalIntegrable (fun t => Real.log ‖g t‖) volume T₁ T₂) :
    (T₂ - T₁) * Real.log c ≤ ∫ t in T₁..T₂, Real.log ‖g t‖ := by
  have hmono : (∫ _t in T₁..T₂, Real.log c) ≤ ∫ t in T₁..T₂, Real.log ‖g t‖ := by
    refine intervalIntegral.integral_mono_on hT _root_.intervalIntegrable_const hint ?_
    intro t ht
    have hmem : t ∈ Set.uIcc T₁ T₂ := by
      rw [Set.uIcc_of_le hT]; exact ht
    exact Real.log_le_log hc (hlow t hmem)
  simpa using hmono

/-- **The right-edge input, in the form the skeleton consumes.**  If `‖g − 1‖ ≤ 1/2` on the edge, the
log-modulus integral is at least `−(log 2)(T₂ − T₁)`. -/
theorem neg_log_two_mul_length_le_integral_log_norm {T₁ T₂ : ℝ} {g : ℝ → ℂ}
    (hT : T₁ ≤ T₂) (hclose : ∀ t ∈ Set.uIcc T₁ T₂, ‖g t - 1‖ ≤ 1 / 2)
    (hint : IntervalIntegrable (fun t => Real.log ‖g t‖) volume T₁ T₂) :
    -(Real.log 2 * (T₂ - T₁)) ≤ ∫ t in T₁..T₂, Real.log ‖g t‖ := by
  have hbase := length_mul_log_le_integral_log_norm (c := 1 / 2) hT (by norm_num)
    (fun t ht => half_le_norm_of_dist_le_half (hclose t ht)) hint
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div one_ne_zero two_ne_zero, Real.log_one]
    ring
  rw [hlog] at hbase
  linarith

end RHTower
