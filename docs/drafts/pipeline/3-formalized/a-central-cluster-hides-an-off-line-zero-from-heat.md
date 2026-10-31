# A central cluster hides an off-line zero from heat `≍ δ²/m`

- **ID:** heat-cluster-hiding
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #2; `reboot-final.md` WP-A falsifier, WP-B
- **Statement:** For `m ∈ ℕ`, `δ ∈ ℝ`, `L ≥ 0` and `64δ² ≤ λ(m + 2)`, the heated model slice
  `E[g(x + √λZ)]`, `g(x) = x^{2m}(δ² − x²)² cosh(Lx)`, has nonnegative Taylor coefficients at `0`,
  although `g(δ) = 0`.

## Lean
Module `RHTower/Heat/AClusterHidesAnOffLineZeroFromHeat.lean` (namespace `RHTower.DeBruijn`):
`hasSum_clusterModelHeat` (main), `clusterModelHeat_eq` (closed form via the Gaussian tilt),
`coeffNonneg_forwardPolyHeat_clusterHead` (head repair), `CoeffNonneg.taylor`,
`hasSum_exp_mul_eval`. Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Paper proof
`g` is the slice at `t₀` of `F(z) = (z−t₀)^m((z−t₀)² + δ²)√2 sin(L(z−t₀)/2 + π/4)`: an `m`-fold zero at
the centre, an off-line pair at depth `δ`, real zeros of density `L/2π`. With `p(x) = x^{2m}(δ²−x²)²`
and `Q = e^{(λ/2)∂²}p`, tilting the Gaussian gives
`H(x) = ½e^{λL²/2}(e^{Lx}Q(x + λL) + e^{−Lx}Q(x − λL))`. `p` is the expansion of `y^m(y − δ²)²`,
`m + 2` roots in `|y| ≤ δ²`, so `Q` has nonnegative coefficients when `32δ² ≤ (λ/2)(m + 2)`
(`coeffNonneg_forwardPolyHeat_expand_of_discFactors`). A Taylor shift to `λL ≥ 0` and the factor
`e^{Lx}` keep the coefficients nonnegative; `Q` is even, so `H` is a positive multiple of the even part
of `e^{Lx}Q(x + λL)`.

## What it changes
At height `t`, `L = log t`, a central zero of multiplicity `m ≍ log t` is allowed by the local count
`≤ 40 log(180t)`. Heated positivity at rate `κ = λL ≍ δ²` then coexists with an off-line zero of depth
`δ`. With `heat-detection-rate-is-quadratic-in-the-depth.md` (detection at `κ ≤ δ²/200`) the order `δ²`
of unconditional heat detection is optimal for configurations with central clusters: the critical
heat is `≍ δ²/(local degree at radius δ)`. A linear rate needs a count of zeros within `O(δ)` of
`½ + it` below `log t` (WP-A1); no size or density input on the repair side changes this.

## Log
- 2026-10-30 — created; proved; formalized.
