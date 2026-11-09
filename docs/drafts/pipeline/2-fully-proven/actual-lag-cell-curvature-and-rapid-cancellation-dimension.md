# Actual lag cell curvature and rapid cancellation dimension

- **Stage:** 2-fully-proven; Lean formalization in progress
- **Type:** THEOREM on paper; not yet counted
- **Obstacles:** B13, B112; unconditional geometry of recurrent cancellation bases.
- **Statement:** The scaled actual lag is strictly concave on every integer cell beyond `2`, with a quantitative second-derivative bound. This gives at most two zeros per cell and makes the positive bases with recurrence at every exponential decay rate Hausdorff-dimension zero, unconditionally.
- **Consequence:** The actual residual rapid-cancellation family has dimension zero independently of AAL. Its small size comes from local arithmetic-cell curvature, not a finite isolated top.

## Corpus evidence

`weilLagFunctionReal_eq_prime_side` expresses the scaled lag as an affine prime term minus `x log x` plus the complete trivial-zero series. `WeilLagQuadraticInterpolation.lean` supplies the arithmetic ramp representation and convexity tools. `FiniteJetSublevelCover.lean` turns a nonzero second derivative into a two-ball sublevel cover. `ZetaResidualSampling.lean` supplies unconditional residual rapid cancellation.

## Proof

Write `Phi(t)=weilLagFunctionReal t` and `S(x)=sum_{k>=1} x^(-2k)/(2k(2k+1))`. On a neighborhood `x>r>1`, both derivative series are dominated by geometric series. Thus differentiation term by term is valid twice:
`S'(x)=-sum_{k>=1} x^(-2k-1)/(2k+1)` and
`S''(x)=sum_{k>=1} x^(-2k-2)=1/(x^2(x^2-1))`.

On the half-open integer cell `[j,j+1)`, the prime-side formula gives
`exp(log(x)/2) Phi(log x)=A_j x+B_j-x log x+S(x)`,
where `A_j=1+gamma+mertensSum(j)` and `B_j=-psi(j)-log(2pi)`. The model on the right is defined for every `x>1`. Its second derivative is `-1/x+1/(x^2(x^2-1))`. For `2<=x<=R`, the inequality `x(x^2-1)>=2` gives
`-model''(x)>=1/(2x)>=1/(2R)`.
Hence the model is strictly concave beyond `2`, and no three distinct points in one cell can all be zeros: strict concavity at the middle point contradicts zero endpoint values.

The order-two sublevel-cover theorem now gives at most two balls covering `|model(x)|<epsilon` on `[2,R]`, each of radius
`2 sqrt(12R) sqrt(epsilon)`.
This estimate is uniform in the affine coefficients, hence uniform in the cell index.

Fix `0<L<=U`, an accuracy index `m`, and a level `n>=1`. Put `R=exp(nU)>=1`. If `ell in [L,U]`, `exp(n ell)>=2`, and `|Phi(n ell)|<=exp(-(m+1)n)`, then its cell model at `x=exp(n ell)` has absolute value at most `R exp(-(m+1)n)`. Use `epsilon=2R exp(-(m+1)n)`. At most `floor(R)+1` cells occur, so at most `4R` balls suffice, with radius
`K R exp(-(m+1)n/2)`, where `K=4 sqrt(6)`.
Replace each center `z` by `max(1,z)`, then apply `log` and divide by `n`. Clipping does not increase distance from `x>=2`; logarithm is 1-Lipschitz on `[1,infinity)`; division by `n>=1` does not increase distance. The same count and radius therefore cover the corresponding bases.

For every `s>0`, choose a natural `m` so large that
`s((m+1)/2-U)>U`.
The total `s`-dimensional diameter cost at level `n` is then at most
`4(2K)^s exp(-(s((m+1)/2-U)-U)n)`, a summable geometric sequence. The finitely many levels with `exp(nL)<2` do not affect recurrence. Every base in the actual rapid-cancellation set meets this fixed accuracy infinitely often, so tail covers give zero `s`-dimensional Hausdorff measure on `[L,U]`. Countably many compact positive intervals cover the positive half-line. Since `s>0` was arbitrary, the positive rapid-cancellation set has Hausdorff dimension zero.

The preceding unconditional residual-recurrence theorem makes this same set dense G-delta and uncountable in every positive open interval. No RH, AAL, or isolated-top assumption occurs in the dimension argument.

## Novelty and formalization gate

The corpus has discrete integer-lag curvature and one-sided chord estimates. The new mechanism is uniform continuous curvature inside arithmetic cells, giving finite sublevel covers and unconditional zero dimension for actual rapid-cancellation bases. The curvature law, cell zero bound, covering estimate, and residual dimension-zero specialization count together. Lean and transitive-axiom audits remain.
