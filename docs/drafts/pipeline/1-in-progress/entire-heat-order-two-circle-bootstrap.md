# Entire-heat order-two exclusion by a circle bootstrap

- **ID:** entire-heat-order-two-circle-bootstrap
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) → THEOREM (Lean)
- **Source:** `2-fully-proven/02-analytic-da-entire-functions/entire-heat-multiplicative-da-order-three-floor.md`
- **Statement:** An infinite-spectrum entire-heat anchor satisfies no order-two ADE; proof by a
  second-jet gap and a continuous bootstrap in the radius, replacing Strelitz's component argument.

## Goal
Close the last open step of card 8 (order two) unconditionally in Lean.

## Paper proof

Notation: `u = zf'/f`, `v = zu'`. The corpus compiler gives a nonzero
`Q ∈ ℂ[z][F,U,V]` with `Q(z; f, u, v) = 0` wherever `f ≠ 0`.

**Step 1 (second-jet gap).** Take the lexicographically largest `(F, z, U)`-exponent of `Q`
and let `s(V) ≠ 0` be the corresponding coefficient polynomial in `V`. For `|z|, |F|, |U| ≥ 1`,
`|U| ≤ B`, `|V| ≤ 1` and `Q = 0`:
`|s(V)| ≤ C((1+|z|)^E B^E/|F| + B^E/|z| + 1/|U|)`.
Write `s = V^m t`, `t(0) ≠ 0`. There is `ρ₀ > 0` such that for every `0 < ρ ≤ ρ₀` there is
`κ > 0`: if the bracket is `≤ κ` and `|V| ≤ ρ`, then `|V| ≤ ρ/2`.

**Step 2 (circle bootstrap).** Suppose on the circle `|z| = r₀` we have `f ≠ 0`,
`|u - N| ≤ 1/4`, `|v| ≤ ρ`, `|f| ≥ (1+r₀)^E (N+2)^E 3/κ`, and `r₀ ≥ 3(N+2)^E/κ`,
`N ≥ max(E+1, 3/κ+1)`, `ρ ≤ min(ρ₀, 1/(16π))`. Let `T` be the set of `r ≥ r₀` whose circle has
`|f| ≥ G(r) := (1+r)^E (N+2)^E 3/κ`, `|v| ≤ ρ`, and circle mean `I(r)` of `u` with
`|I(r) - N| ≤ 1/4`.
- On such a circle, `u(re^{iθ})` has `θ`-derivative `i v`, so `|u - I(r)| ≤ 3πρ` and `|u - N| ≤ 1/2`.
- Step 1 applies, so `|v| ≤ ρ/2`.
- `T` is closed. `I` is locally constant near zero-free circles because it is `(2πi)⁻¹∮ f'/f`.
- `T` is open to the right. Strictness and continuity near the circle, local constancy of `I`,
  and the radial derivative `d/dlog r log|f| = Re u ≥ N - 1/2 > E ≥ d/dlog r log G` give this.

Continuous induction therefore gives `T ⊇ [r₀, ∞)`. Radial integration gives
`|f(z)| ≤ M₀ (|z|/r₀)^{N+1/2}`, and Cauchy's estimate makes `f` a polynomial.

**Step 3 (heat clean circles).** The central index satisfies `ν(e^x) = o(x)` and is monotone.
Pigeonhole on blocks of length `2D` gives arbitrarily large `x` with `ν(e^{x-D}) = ν(e^{x+D}) = n`.
Hence `|a_i| r^i ≤ e^{-D|i-n|} |a_n| r^n` at `r = e^x`. With `q = e^{-D}` and weights
`j^k q^j ≤ (4q)^j`:
- `|f| ≥ μ/2`;
- `|u - n| ≤ 32q`;
- `|v| ≤ 64q`, via `v = (G₂f - G₁²)/f²` with `G_k = Σ (i-n)^k a_i z^i`.

A fixed large `D`, together with `μ(r) ≥ |a_j| r^j` for `j ≥ 2E+1` and `n = o(log r)`, meets every
Step 2 hypothesis. So an infinite-spectrum heat anchor has no order-two ADE.

## Lean plan
1. `HTGeometry/StrelitzSecondJetGap.lean`: Step 1.
2. `HTGeometry/StrelitzCircleBootstrap.lean`: Step 2 (mean, angular/radial integration, induction).
3. `HTGeometry/EntireHeatCleanCircle.lean`: Step 3 (pigeonhole, dominance, jet bounds).
4. `HTGeometry/EntireHeatOrderTwoFloor.lean`: the capstone `¬ DifferentiallyAlgebraicOfOrder (coeffFun a) 2`
   and the full card statement for orders `≤ 2`.

## Log
- 2026-09-29 — created; the paper proof above replaces the Strelitz enlarged-set component
  argument for the heat class. It uses only the corpus log-jet compiler, the central-index asymptotic
  and elementary circle analysis.
