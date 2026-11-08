# Integer rounding retains the finite prime oscillation

- **ID:** integer-rounding-retains-prime-oscillation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every real `γ`, the existing integer-norm Euler product with exactly the zeros `3/5 ± iγ` in `Re s>1/2`, away from `1`, has

`ϑ_q(n) = n + n^(3/5) Ω_γ(log n) + O_ε(n^ε)`

for every `ε>0` and integer `n≥1`, where

`Ω_γ(t) = -2 ((3/5) cos(γt) + γ sin(γt)) / ((3/5)^2 + γ^2)`.

Here `ϑ_q(n)=Σ_(q_k≤n) log q_k`, with prime-label multiplicities retained.
The oscillation is nonzero: `Ω_γ(0)<0`.

## Proof

Write `N(t)=floor(W(t))`, `W(t)=∫₀ᵗ w`, and `W(t_k)=k+1`.
Finite summation and integration by parts give

`Σ_(t_k≤t) t_k − ∫₀ᵗ u w(u) du = t(N−W)(t) − ∫₀ᵗ (N−W)(u) du`.

Since `-1≤N−W≤0`, its absolute value is at most `t`.
At integer horizon `n`, `ceil(exp(t_k))≤n` exactly when `t_k≤log n`.
The weight drift is nonnegative, and for every `ε>0`,

`Σ_(t_k≤t) (log q_k−t_k) ≤ exp(εt) Σ_k exp(-(1+ε)t_k)`.

The series converges by the existing prime-sum theorem. Integrating the
explicit exponential-cosine density gives the displayed oscillation;
the remaining density terms contribute at most a constant plus `2t`.
Thus the total error is bounded by `K+3t+S_ε exp(εt)`.
Using `t≤exp(εt)/ε` gives the stated bound. The proof does not assert
a constant limit for the accumulated rounding drift.

## Lean

Module: `ArithmeticPositiveDuality/IntegerRoundingPreservesWeightedPrimeCounts.lean`.

- `abs_discretePrimeTheta_sub_continuous_le`: weighted quantile discrepancy.
- `integerPrimeTheta_finiteOscillation`: explicit oscillation for all admissible parameters.
- `integer_norm_one_off_with_prime_oscillation`: closed joint certificate with integer norms, Euler product, analytic continuation, exact zero pair, explicit trigonometric polynomial, and subpower error.

Direct `lake --old env lean` audit passes without warnings. All three
capstones have exactly `propext`, `Classical.choice`, and `Quot.sound`.
The module is imported by its umbrella; no olean or umbrella build was needed.

## Relevance and remaining gap

This certifies the useful core of worklog cycle 235 for the literal
integer-norm model. Integer support permits a finite leading prime
oscillation. The labels may be composite or repeated. Exact unit
Dirichlet coefficients and the Riemann functional equation remain separate
requirements. AAL for actual zeta is unresolved.
