import Mathlib

/-!
# Positivity of a counting function bounds the linear coefficient of its asymptotic

A Riemann–von Mangoldt count has the shape `A·T·log T + B·T + E(T)` with `|E(T)|` logarithmic.
Because a count is never negative, the linear coefficient `B` cannot be very negative: evaluating
at a single height `T₀` and dividing by `T₀` gives

```text
B ≥ -A·log T₀ - C·(1 + log (T₀ + 2)) / T₀ ,
```

and the choice `T₀ = 1` kills the `A`-term entirely, leaving `B ≥ -C·(1 + log 3)`, a bound
depending only on the size of the error term.

For a zero-counting function `A = d/2π` and `B = (log q)/2π` with `q` the conductor, so the
conclusion reads `q ≥ exp(-2π·C·(1 + log 3))`: **a nonnegative zero count forces a positive lower
bound on the conductor**, with the bound governed solely by the uniformity of the error term.
-/

namespace HTGeometry

/-- **Positivity at one height bounds the linear coefficient.** -/
theorem linear_coeff_ge_of_nonneg {A B C : ℝ}
    (h : ∀ T : ℝ, 0 < T → 0 ≤ A * T * Real.log T + B * T + C * (1 + Real.log (T + 2)))
    {T₀ : ℝ} (hT₀ : 0 < T₀) :
    -A * Real.log T₀ - C * (1 + Real.log (T₀ + 2)) / T₀ ≤ B := by
  have hT := h T₀ hT₀
  rw [← sub_nonneg]
  have hrw : B - (-A * Real.log T₀ - C * (1 + Real.log (T₀ + 2)) / T₀)
      = (B * T₀ - (-A * T₀ * Real.log T₀ - C * (1 + Real.log (T₀ + 2)))) / T₀ := by
    field_simp
  rw [hrw]
  exact div_nonneg (by linarith) (le_of_lt hT₀)

/-- Evaluating at `T₀ = 1` removes the `A`-term: the linear coefficient is bounded below by a
constant depending only on the error term. -/
theorem linear_coeff_ge_of_nonneg_at_one {A B C : ℝ}
    (h : ∀ T : ℝ, 0 < T → 0 ≤ A * T * Real.log T + B * T + C * (1 + Real.log (T + 2))) :
    -(C * (1 + Real.log 3)) ≤ B := by
  have hT := h 1 one_pos
  norm_num at hT
  linarith

/-- **Conductor lower bound.**  If the count `A·T·log T + ((log q)/(2π))·T + E(T)` is nonnegative
for every positive height and the error is bounded by `C·(1 + log (T+2))`, then
`q ≥ exp (-2π·C·(1 + log 3))`. -/
theorem conductor_ge_of_count_nonneg {A C q : ℝ} (hq : 0 < q)
    (h : ∀ T : ℝ, 0 < T →
      0 ≤ A * T * Real.log T + (Real.log q / (2 * Real.pi)) * T + C * (1 + Real.log (T + 2))) :
    Real.exp (-(2 * Real.pi * (C * (1 + Real.log 3)))) ≤ q := by
  have hB := linear_coeff_ge_of_nonneg_at_one h
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlog : -(2 * Real.pi * (C * (1 + Real.log 3))) ≤ Real.log q := by
    have hmul := mul_le_mul_of_nonneg_left hB (le_of_lt hpi)
    have hcancel : 2 * Real.pi * (Real.log q / (2 * Real.pi)) = Real.log q := by
      field_simp
    rw [hcancel] at hmul
    have heq : 2 * Real.pi * -(C * (1 + Real.log 3))
        = -(2 * Real.pi * (C * (1 + Real.log 3))) := by ring
    linarith [hmul, heq.symm.le, heq.le]
  calc Real.exp (-(2 * Real.pi * (C * (1 + Real.log 3))))
      ≤ Real.exp (Real.log q) := Real.exp_le_exp.mpr hlog
    _ = q := Real.exp_log hq

end HTGeometry
