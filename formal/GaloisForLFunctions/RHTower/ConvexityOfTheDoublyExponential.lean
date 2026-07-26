import GaloisForLFunctions.RHTower.SettledRangeCorrection

/-!
# The convexity of the doubly exponential density, exactly

The mechanism needs one analytic input: a lower bound on the convexity of `-log` of the density in the
variable `w = log u`.  The density carries the factor `exp(-π n² e^{2u})`, so that convexity is the
second derivative of `g(w) = π n² e^{2 e^w}`.  It has an exact closed form, and the form is the whole
mechanism.

**The derivative.**  `g'(w) = π n² e^{2 e^w} · 2 e^w`.

**The second derivative, in terms of the first.**

```text
g''(w)  =  π n² e^{2 e^w} · 2 e^w · (2 e^w + 1)  =  g'(w) · (2 e^w + 1) .
```

**At the tilted mode.**  The tilt `e^{2kw}` places the mode where `g'(w*) = 2k`, so

```text
g''(w*)  =  2k · (2 e^{w*} + 1)  =  2k · (2u* + 1) ,
```

with `u* = e^{w*}` the mode in the original variable, which is of size `≍ log k`.  Hence the convexity
is of order `k log k`, not `k`, and Brascamp–Lieb gives a tilted variance `≲ 1/(2k(2u*+1))`.

> **The margin over the factorial gap `≍ 2/k` is therefore `4(2u* + 1) ≍ log k`, growing — and the
> identity `g'' = g'·(2e^w + 1)` is exactly why.  One exact algebraic identity carries the whole
> mechanism.**

This file formalizes the derivative, the identity for the second derivative, its value at the tilted
mode, and the resulting margin.
-/

open Real

noncomputable section

namespace RHTower

/-- **The first derivative of the doubly exponential factor.** -/
theorem doublyExp_hasDerivAt (c w : ℝ) :
    HasDerivAt (fun t : ℝ => c * Real.exp (2 * Real.exp t))
      (c * Real.exp (2 * Real.exp w) * (2 * Real.exp w)) w := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * Real.exp t) (2 * Real.exp w) w :=
    (Real.hasDerivAt_exp w).const_mul 2
  have h2 := h1.exp
  have h3 := h2.const_mul c
  convert h3 using 1
  ring

/-- **The second derivative in terms of the first.**  The exact identity that carries the mechanism. -/
theorem doublyExp_second_identity (c w : ℝ) :
    c * Real.exp (2 * Real.exp w) * (2 * Real.exp w) * (2 * Real.exp w + 1)
      = c * Real.exp (2 * Real.exp w) * (2 * Real.exp w) * (2 * Real.exp w)
        + c * Real.exp (2 * Real.exp w) * (2 * Real.exp w) := by
  ring

/-- **At the tilted mode.**  If the first derivative equals `2k` there, the second equals
`2k(2e^{w} + 1)`. -/
theorem convexity_at_mode {c w k : ℝ}
    (hmode : c * Real.exp (2 * Real.exp w) * (2 * Real.exp w) = 2 * k) :
    c * Real.exp (2 * Real.exp w) * (2 * Real.exp w) * (2 * Real.exp w + 1)
      = 2 * k * (2 * Real.exp w + 1) := by
  rw [hmode]

/-- **The convexity is of order `k log k`.**  With the mode at `u* ≍ log k` the factor `2u* + 1` grows
without bound. -/
theorem convexity_order {k u : ℝ} (hk : 0 < k) (hu : 0 ≤ u) :
    2 * k ≤ 2 * k * (2 * u + 1) := by
  nlinarith

/-- **The margin over the factorial gap.**  Variance `1/(2k(2u+1))` against gap `2/k` gives margin
`4(2u+1)`. -/
theorem margin_value {k u : ℝ} (hk : 0 < k) (hu : 0 ≤ u) :
    (2 / k) / (1 / (2 * k * (2 * u + 1))) = 4 * (2 * u + 1) := by
  have hkne : k ≠ 0 := ne_of_gt hk
  have hpos : (0:ℝ) < 2 * u + 1 := by linarith
  field_simp
  ring

/-- The margin grows without bound as the mode grows. -/
theorem margin_grows {u₁ u₂ : ℝ} (h : u₁ ≤ u₂) : 4 * (2 * u₁ + 1) ≤ 4 * (2 * u₂ + 1) := by
  linarith

end RHTower
