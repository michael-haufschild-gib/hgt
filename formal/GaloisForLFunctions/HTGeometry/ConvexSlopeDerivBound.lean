import Mathlib

/-!
# A one-sided derivative bound for a convex function from two-point data

If `φ` is convex and one knows an upper bound for `φ` at `b/2` and a lower bound for `φ` at `b`,
then the derivative at `b` cannot be very negative:
`-φ'(b) ≤ 2(U - L)/b`.

This is the step that converts growth information about a convex function into a bound on its
derivative.  For an analytic almost periodic function on a strip, Jessen's function
`φ(b) = mean over the horizontal line at depth b of log|Φ|` is convex, and by the Jessen–Tornehave
theorem the density of zeros of `Φ` per unit horizontal length between two depths is
`(φ'(b₂) - φ'(b₁))/2π`.  An upper bound for `φ` near the boundary together with a lower bound
further inside therefore bounds the zero density — which is how an `L²` growth rate controls an
integer-valued counting function.
-/

open Set

namespace HTGeometry

/-- **Derivative bound from convexity and two-point data.**  For `φ` convex on `S` with
`b/2, b ∈ S`, differentiable at `b`, and `φ (b/2) ≤ U`, `L ≤ φ b`, one has
`-deriv φ b ≤ 2 (U - L) / b`. -/
theorem neg_deriv_le_of_convexOn {S : Set ℝ} {φ : ℝ → ℝ} {b U L : ℝ}
    (hb : 0 < b) (hconv : ConvexOn ℝ S φ) (hhalf : b / 2 ∈ S) (hmem : b ∈ S)
    (hdiff : DifferentiableAt ℝ φ b) (hU : φ (b / 2) ≤ U) (hL : L ≤ φ b) :
    -deriv φ b ≤ 2 * (U - L) / b := by
  have hlt : b / 2 < b := by linarith
  have h := hconv.slope_le_deriv hhalf hmem hlt hdiff
  rw [slope_def_field] at h
  have hpos : (0 : ℝ) < b - b / 2 := by linarith
  have h2 : φ b - φ (b / 2) ≤ deriv φ b * (b - b / 2) :=
    (div_le_iff₀ hpos).1 h
  have h3 : -deriv φ b * (b / 2) ≤ U - L := by
    have : b - b / 2 = b / 2 := by ring
    rw [this] at h2
    linarith
  rw [le_div_iff₀ hb]
  linarith

/-- **Zero-density bound.**  In the Jessen setting the density of zeros between depth `b` and the
asymptotic regime is `(s - φ'(b))/2π` where `s` is the limiting slope.  With `φ (b/2) ≤ U` and
`φ b ≥ -K·b` this is at most `(s + 2(U + K·b)/b)/2π`. -/
theorem jessen_zero_density_le {S : Set ℝ} {φ : ℝ → ℝ} {b U K s : ℝ}
    (hb : 0 < b) (hconv : ConvexOn ℝ S φ) (hhalf : b / 2 ∈ S) (hmem : b ∈ S)
    (hdiff : DifferentiableAt ℝ φ b) (hU : φ (b / 2) ≤ U) (hL : -(K * b) ≤ φ b) :
    (s - deriv φ b) / (2 * Real.pi) ≤ (s + 2 * (U + K * b) / b) / (2 * Real.pi) := by
  have h := neg_deriv_le_of_convexOn hb hconv hhalf hmem hdiff hU hL
  have hstep : -deriv φ b ≤ 2 * (U + K * b) / b := by
    have hrw : U - -(K * b) = U + K * b := by ring
    rwa [hrw] at h
  have hnum : s - deriv φ b ≤ s + 2 * (U + K * b) / b := by linarith
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  gcongr

end HTGeometry
