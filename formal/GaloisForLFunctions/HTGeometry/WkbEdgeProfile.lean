import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The WKB edge profile: a trial function with squared-small boundary value

A truncated Gaussian is concentrated in frequency but pays for its endpoint value: with
`c = 2πa²` the Gaussian has `e^{−πx²}|_{x=a} = e^{−c/2}`, and an endpoint jump of that size
produces out-of-band Fourier mass of order `e^{−c}` — a factor `2` off the classical `e^{−2c}`
in the exponent.

The prolate ground state does better because the Gaussian only describes it in the *bulk*.  Its
WKB profile is `exp(−c·φ(x/a))` with

```text
φ(u) = 1 − √(1 − u²),
```

which satisfies `φ(u) ≈ u²/2` near `0` — reproducing `e^{−πx²}` — but `φ(1) = 1`, so the edge
value is `e^{−c}` rather than `e^{−c/2}`.  Squaring that edge value gives `e^{−2c}`, the correct
rate.

This module defines that profile and records the two properties that make it a usable trial
function: it is dominated pointwise by the Gaussian (so it inherits frequency concentration),
and its value at the aperture edge is exactly `e^{−c}`.
-/

open scoped Real

noncomputable section

namespace GaloisForLFunctions

/-- The WKB exponent `φ(u) = 1 − √(1 − u²)`. -/
def wkbExponent (u : ℝ) : ℝ := 1 - Real.sqrt (1 - u ^ 2)

/-- The WKB edge profile at aperture `a`: `exp(−2πa²·φ(x/a))`. -/
def wkbEdgeProfile (a x : ℝ) : ℝ :=
  Real.exp (-(2 * π * a ^ 2) * wkbExponent (x / a))

theorem wkbEdgeProfile_pos (a x : ℝ) : 0 < wkbEdgeProfile a x := Real.exp_pos _

/-- On the unit interval the WKB exponent dominates the quadratic one: `1 − √(1−u²) ≥ u²/2`. -/
theorem sq_div_two_le_wkbExponent {u : ℝ} (hu : |u| ≤ 1) :
    u ^ 2 / 2 ≤ wkbExponent u := by
  have hu2 : u ^ 2 ≤ 1 := by
    have := abs_le_one_iff_mul_self_le_one.mp hu
    nlinarith [sq_abs u]
  have hnn : (0 : ℝ) ≤ 1 - u ^ 2 := by linarith
  have hbase : (0 : ℝ) ≤ 1 - u ^ 2 / 2 := by nlinarith
  have hsq : Real.sqrt (1 - u ^ 2) ≤ 1 - u ^ 2 / 2 := by
    rw [show (1 : ℝ) - u ^ 2 / 2 = Real.sqrt ((1 - u ^ 2 / 2) ^ 2) from
      (Real.sqrt_sq hbase).symm]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (u ^ 2)]
  unfold wkbExponent
  linarith

/-- The WKB exponent is nonnegative on the unit interval. -/
theorem wkbExponent_nonneg {u : ℝ} (hu : |u| ≤ 1) : 0 ≤ wkbExponent u :=
  le_trans (by positivity) (sq_div_two_le_wkbExponent hu)

/-- **The profile is dominated by the Gaussian.**  Inside the aperture the WKB profile never
exceeds `e^{−πx²}`, so it inherits the Gaussian's frequency concentration. -/
theorem wkbEdgeProfile_le_gauss {a x : ℝ} (ha : 0 < a) (hx : |x| ≤ a) :
    wkbEdgeProfile a x ≤ Real.exp (-(π * x ^ 2)) := by
  have hu : |x / a| ≤ 1 := by
    rw [abs_div, abs_of_pos ha, div_le_one ha]
    exact hx
  have hφ := sq_div_two_le_wkbExponent hu
  have hkey : π * x ^ 2 ≤ (2 * π * a ^ 2) * wkbExponent (x / a) := by
    have hstep : (2 * π * a ^ 2) * ((x / a) ^ 2 / 2)
        ≤ (2 * π * a ^ 2) * wkbExponent (x / a) :=
      mul_le_mul_of_nonneg_left hφ (by positivity)
    have heq : (2 * π * a ^ 2) * ((x / a) ^ 2 / 2) = π * x ^ 2 := by
      field_simp
    linarith [hstep, heq.le, heq.ge]
  unfold wkbEdgeProfile
  rw [Real.exp_le_exp]
  linarith

/-- **The edge value is `e^{−2πa²}`** — the square root of the target leakage, which is exactly
what a truncated Gaussian fails to achieve. -/
theorem wkbEdgeProfile_edge {a : ℝ} (ha : a ≠ 0) :
    wkbEdgeProfile a a = Real.exp (-(2 * π * a ^ 2)) := by
  unfold wkbEdgeProfile wkbExponent
  rw [div_self ha]
  norm_num

/-- At the centre the profile is one, matching the Gaussian. -/
theorem wkbEdgeProfile_center (a : ℝ) : wkbEdgeProfile a 0 = 1 := by
  unfold wkbEdgeProfile wkbExponent
  rw [zero_div]
  norm_num

/-- The profile is at most one on the aperture. -/
theorem wkbEdgeProfile_le_one {a x : ℝ} (ha : 0 < a) (hx : |x| ≤ a) :
    wkbEdgeProfile a x ≤ 1 := by
  have hle := wkbEdgeProfile_le_gauss ha hx
  have : Real.exp (-(π * x ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : (0 : ℝ) ≤ π * x ^ 2 := by positivity
    linarith
  linarith

end GaloisForLFunctions
