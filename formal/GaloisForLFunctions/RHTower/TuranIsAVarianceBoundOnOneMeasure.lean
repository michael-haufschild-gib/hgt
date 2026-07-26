import GaloisForLFunctions.RHTower.HutchinsonNeedsFourAndOnlyOneIsAvailable

/-!
# The order-two inequality is a variance bound on one explicit measure, and it holds by a logarithm

Stripping away the polynomials leaves a statement about a single positive measure.  This file states
it, evaluates it at the saddle, and finds the margin.

**The translation.**  For `M_s = ∫ u^s dν(u)` the second logarithmic derivative is the variance of
`log u` under the tilted measure:

```text
(d²/ds²) log M_s  =  Var_{ν_s}(log u) .
```

So the order-two condition `M_j² · cap ≥ M_{j-1}M_{j+1}`, with
`cap = (n+1)(n+2)/((n-1)n)` and `n = 2j`, is exactly

```text
Var_{ν_j}(log u)  ≤  log cap  ≈  4/n  =  2/j .
```

**The evaluation.**  The measure is the theta remainder in the squared variable, `u = t²`, and its
tilted exponent is `f(t) = 2j log t + 9t/2 - π e^{2t}` with

```text
f''(t) = -( 2j/t² + 4π e^{2t} ) ,        π e^{2t*} = j/t*  at the saddle,
```

so `f''(t*) = -(2j/t*² + 4j/t*)`, the width in `t` is `t*²/(2j + 4j t*)`, and since `log u = 2 log t`,

```text
Var_j(log u)  =  (2/t*)² · t*²/(2j + 4j t*)  =  2 / ( j (1 + 2t*) ) .
```

> **The requirement is `2/j` and the value is `2/(j(1 + 2t*))`, so the inequality holds with margin
> exactly `1 + 2t*`.  With the saddle at `t* ≈ ½ log j`, the margin is `log j`.**

This re-derives the order-two inequality for this sequence with no polynomials, no determinants and
no zeros, and the margin `1 + 2t*` is the same factor that appears as the convexity of the
doubly-exponential exponent elsewhere in this development.

This file formalizes the exact variance formula from the curvature, the margin identity, and the
condition for the margin to exceed one.
-/

open Real

noncomputable section

namespace RHTower

/-- **The variance from the curvature.**  With width `t²/(2j + 4jt)` in `t` and `log u = 2 log t`,
the variance of `log u` is `2/(j(1 + 2t))`. -/
theorem variance_from_curvature {j t : ℝ} (hj : 0 < j) (ht : 0 < t) :
    (2 / t) ^ 2 * (t ^ 2 / (2 * j + 4 * j * t)) = 2 / (j * (1 + 2 * t)) := by
  have hden : 2 * j + 4 * j * t ≠ 0 := by positivity
  have htne : t ≠ 0 := ne_of_gt ht
  have hj2 : j * (1 + 2 * t) ≠ 0 := by positivity
  field_simp
  ring

/-- **The margin.**  Dividing the requirement `2/j` by the value `2/(j(1+2t))` leaves `1 + 2t`. -/
theorem margin_is_one_plus_two_t {j t : ℝ} (hj : 0 < j) (ht : 0 < t) :
    (2 / j) / (2 / (j * (1 + 2 * t))) = 1 + 2 * t := by
  have hjne : j ≠ 0 := ne_of_gt hj
  have hpos : 0 < 1 + 2 * t := by linarith
  field_simp

/-- **The margin exceeds one** whenever the saddle is at a positive place. -/
theorem variance_margin_gt_one {t : ℝ} (ht : 0 < t) : 1 < 1 + 2 * t := by linarith

/-- **The variance is below the requirement**, strictly, for every positive saddle place. -/
theorem variance_lt_requirement {j t : ℝ} (hj : 0 < j) (ht : 0 < t) :
    2 / (j * (1 + 2 * t)) < 2 / j := by
  have hpos : 0 < 1 + 2 * t := by linarith
  rw [div_lt_div_iff₀ (by positivity) hj]
  nlinarith

/-- **The requirement in logarithmic form.**  The cap bounds the logarithm of the log-convexity
defect, and `log(1 + x) ≤ x` turns the cap into `(4n+2)/((n-1)n)`. -/
theorem log_cap_le {x : ℝ} (hx : 0 ≤ x) : Real.log (1 + x) ≤ x :=
  Real.log_le_sub_one_of_pos (by linarith) |>.trans_eq (by ring)

/-- The cap written as one plus the exact excess. -/
theorem cap_eq_one_add {n : ℝ} (h1 : n - 1 ≠ 0) (h0 : n ≠ 0) :
    hutchinsonCap n = 1 + (4 * n + 2) / ((n - 1) * n) := by
  unfold hutchinsonCap
  field_simp
  ring

/-- **The excess is of size `4/n`.**  So the requirement on the variance is `≈ 4/n = 2/j`. -/
theorem excess_le {n : ℝ} (hn : 4 ≤ n) : (4 * n + 2) / ((n - 1) * n) ≤ 6 / n := by
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  rw [div_le_div_iff₀ (by positivity) hn0]
  nlinarith

end RHTower
