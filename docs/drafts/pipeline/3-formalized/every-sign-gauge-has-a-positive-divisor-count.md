# Every sign gauge has a positive divisor count

- **ID:** every-sign-gauge-has-a-positive-divisor-count
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Γ12; positive renewal route at zero relative logarithmic density.
- **Statement:** For every completely multiplicative real sign gauge `ω`, `g(n)=Σ_(d|n)ω(d)≥0` and `Σ_(n≤N)ω(n)/n≥−1` at every horizon.

## Proof

The multiplicative function `g=1*ω` has prime-power factors
`Σ_(j=0)^k ω(p)^j`: either `k+1` or an alternating sum in `{0,1}`.
Thus every coefficient is nonnegative. Divisor swapping gives
`Σ_(n≤N)g(n)=Σ_(d≤N)ω(d)⌊N/d⌋`. Each rounding error in
`NΣω(d)/d` has absolute value at most one, so the total error is at
most `N`. Nonnegativity of the count gives the lower bound.

## Positive renewal identity

The logarithmic derivative of `g=1*ω` is `K=(1+ω)Λ≥0`.
The convolution product rule and `Λ*1=log` give
`g(n)log n=Σ_(d|n)K(d)g(n/d)`. Summing after division by `n` yields

`Σ_(n≤N)g(n)log n/n=Σ_(d≤N)(K(d)/d)Σ_(m≤N/d)g(m)/m`.

Both the coefficients and the renewal kernel are nonnegative.

## Lean

`ArithmeticCountingPositivity/EveryPrimeFlipHasAPositiveDivisorCount.lean`:

- `signDivisorCount_nonneg`
- `sum_signDivisorCount_eq`
- `abs_mul_gaugeHarmonicSum_sub_signDivisorCount_le`
- `neg_one_le_gaugeHarmonicSum`

`ArithmeticCountingPositivity/TheDivisorCountHasAPositiveRenewalKernel.lean`:

- `signDivisorCount_one`
- `signRenewalKernel_nonneg`
- `signDivisorCount_mul_log`
- `signDivisorCount_logMoment_eq`

Kernel check passed; capstones use only `propext`, `Classical.choice`,
and `Quot.sound`.

These are the finite positivity inputs to the renewal route. They prove
neither eventual positivity nor regular variation of the signed sum.
