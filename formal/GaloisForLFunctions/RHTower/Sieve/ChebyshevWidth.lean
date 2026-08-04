import GaloisForLFunctions.RHTower.Sieve.ChebyshevHeight

/-!
# The balanced smoothing width

The cutoff is smoothed over

    H(x) = x / exp((log x)^{1/20}),

so that the ratio `x/H(x)` is `exp(√t)` with `t = (log x)^{1/10}` the exponent of the truncation
height.  The decay constant of the cutoff's transform carries `(x/H)²`, hence `exp(2√t)`, and the
contour's saving is `exp(-At)`; the square root is what makes the first negligible against the
second.

The same width keeps the sharp-versus-smooth error `H·log x` of size `x·(log x)/exp(√t)`, which is
`o(x)` because `log x = t^{10}`.
-/

namespace RHTower.Sieve

open Filter Topology

/-- The balanced smoothing width attached to a cutoff of size `x`. -/
noncomputable def chebWidth (x : ℝ) : ℝ := x / Real.exp ((Real.log x) ^ ((1 : ℝ) / 20))

/-- The width is positive. -/
theorem chebWidth_pos {x : ℝ} (hx : 0 < x) : 0 < chebWidth x := by
  rw [chebWidth]
  positivity

/-- The width is at most the cutoff. -/
theorem chebWidth_le {x : ℝ} (hx : 0 ≤ Real.log x) (hx0 : 0 < x) : chebWidth x ≤ x := by
  rw [chebWidth, div_le_iff₀ (Real.exp_pos _)]
  have h1 : (1 : ℝ) ≤ Real.exp ((Real.log x) ^ ((1 : ℝ) / 20)) :=
    Real.one_le_exp (by positivity)
  nlinarith

/-- The ratio of cutoff to width is the square-root exponential. -/
theorem div_chebWidth {x : ℝ} (hx0 : 0 < x) :
    x / chebWidth x = Real.exp ((Real.log x) ^ ((1 : ℝ) / 20)) := by
  rw [chebWidth, div_div_eq_mul_div]
  field_simp

/-- The width's exponent is the square root of the height's. -/
theorem sqrt_logRoot {u : ℝ} (hu : 0 ≤ u) :
    Real.sqrt (u ^ ((1 : ℝ) / 10)) = u ^ ((1 : ℝ) / 20) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hu]
  norm_num

end RHTower.Sieve
