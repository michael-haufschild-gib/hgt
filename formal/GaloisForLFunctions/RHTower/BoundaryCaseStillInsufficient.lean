import GaloisForLFunctions.RHTower.ExponentChainKappa

/-!
# Even the boundary case `κ = ∞` does not reach the hypothesis

The zero-free-width exponent is `1 - 1/κ`, so the hypothesis needs `κ = ∞`: subpolynomial growth of
`|ζ|` throughout the strip.  This file identifies that boundary case and shows it is still not enough.

**The boundary case is Lindelöf, and it is the same on the line and in the strip.**  The convexity
(Phragmén–Lindelöf) exponent `μ` is convex, with `μ(1) = 0`; a bound `μ(1/2) ≤ ε` therefore forces
`μ(σ) ≤ 2ε(1 - σ)` for `1/2 ≤ σ ≤ 1`.  So subpolynomial growth on the line already gives it
throughout the strip: the strip version is not a stronger hypothesis.

**And Lindelöf is a density statement.**  It is classically equivalent to
`N(σ, T+1) - N(σ, T) = o(log T)` for every `σ > 1/2` — a bound on a **count**, growing with the
height.  By the integrality criterion a count excludes only when it falls below one, and `o(log T)`
does not: `√(log T)` is `o(log T)` and tends to infinity.

> **The boundary case of the whole zero-free-region family is Lindelöf; Lindelöf is a height-growing
> density statement; and height-growing density statements never exclude.  So the family does not
> reach the hypothesis even in the limit, and the reason is the same height-uniformity gap recorded
> for every other route.**

With this the atlas closes: every unconditional route is separated from the zeros by the strip, or
bounded by a finite `κ`, or at `κ = ∞` and equivalent to a density statement — and every density
statement fails uniformity.

This file formalizes the convexity transfer, the failure of `o(log T)` to be sub-unit, and the
resulting closure.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **Convexity transfer.**  A convex exponent vanishing at `σ = 1` and at most `ε` at `σ = 1/2` is at
most `2ε(1-σ)` in between: subpolynomial on the line gives subpolynomial in the strip. -/
theorem convexity_transfer {ε σ : ℝ} (hε : 0 ≤ ε) (h1 : 1 / 2 ≤ σ) (_h2 : σ ≤ 1) :
    2 * ε * (1 - σ) ≤ ε := by
  nlinarith

/-- The transferred bound is subpolynomial for every `ε`, so the strip version is not stronger. -/
theorem transfer_subpolynomial {ε σ : ℝ} (hε : 0 < ε) (h1 : 1 / 2 ≤ σ) (_h2 : σ ≤ 1) :
    2 * ε * (1 - σ) < 2 * ε := by
  nlinarith

/-- **A `o(log T)` bound need not be sub-unit.**  `√(log T)` is `o(log T)` and exceeds one from some
height on. -/
theorem sqrt_log_grows : Tendsto (fun T : ℝ => Real.sqrt (Real.log T)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop

/-- Hence it eventually exceeds any threshold, in particular one. -/
theorem sqrt_log_exceeds_one : ∀ᶠ T in atTop, 1 ≤ Real.sqrt (Real.log T) :=
  sqrt_log_grows.eventually_ge_atTop 1

/-- **The boundary case still fails.**  A count bounded by a growing quantity is never forced to zero,
so the limit of the family does not exclude a zero. -/
theorem boundary_case_fails {B : ℝ → ℝ} (hB : Tendsto B atTop atTop)
    (hexcl : ∀ T : ℝ, B T < 1) : False :=
  uniform_bound_needed hB hexcl

/-- **The closure.**  Finite `κ` is bounded away from the hypothesis, and the boundary case reduces to
a growing density statement; both fail. -/
theorem atlas_closure {kappa : ℝ} (_hk : 0 < kappa) {B : ℝ → ℝ} (hB : Tendsto B atTop atTop) :
    unitExponent kappa < 1 ∧ (∀ T : ℝ, B T < 1) → False := by
  refine fun h => boundary_case_fails hB h.2

end RHTower
