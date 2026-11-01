# Do logarithmic Chebyshev bands detect every zero?

- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Parent:** [Argon routes](../1-in-progress/argon-quasi-rh-and-critical-proportion.md), §3B.

## Target

The actual packet `chebyshevCyclotomicNear(N, ceil(log(N+1)))` has energy abscissa
`2Θ` among exponents at least one. Existing proofs establish this only for positive
power cutoffs; their far-tail estimate gives no strict exponent saving here.

## Possible mechanism

A fixed nonzero Fourier mode of the prefix packet should be a Mellin convolution
of the Chebyshev error with `1−exp(2πikx)`. A zero ρ with `Re ρ>1/2` contributes
a Mellin factor

`H_k(ρ−1/2)=∫₀¹ x^(ρ−3/2)(1−exp(2πikx)) dx`.

Integration by parts relates this factor to a nonconstant Fourier coefficient of
`x^(ρ−1/2)`. Fourier completeness prevents all nonzero integer modes from having
zero factor simultaneously: that would make this nonconstant function constant.
A logarithmic band eventually contains each fixed detecting mode.

## Exact gaps

Prove the discrete moving-root packet's Mellin identity, control interpolation
errors below the relevant energy exponent, and exclude pole cancellation for a
mode with nonzero factor. Fourier completeness alone supplies none of these
analytic bridges. No fixed-mode or logarithmic-band theorem is asserted.

Corpus search found the existing power-band localization and related Chebyshev
Mellin transforms, but no matching logarithmic-band result. This is a localization
target, not a new arithmetic upper bound or an improved zero-free strip.
