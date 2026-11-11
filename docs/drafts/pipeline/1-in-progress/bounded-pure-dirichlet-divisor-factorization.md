# A finite exponential divisor for a bounded pure Dirichlet series

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [Closure tasks](../3-formalized/fable-route-closures.md).

## Remaining conjecture

Let `x<c`, and let nonzero `F` be holomorphic and bounded on `Re s>x`,
with an ordinary Dirichlet series absolutely convergent sufficiently far right.
Suppose every zero of `F` in this half-plane has real part `c`.
Does a nonzero finite exponential polynomial with real frequencies have exactly
its zero divisor in the half-plane?

This stronger divisor statement remains unproved.

## Proven sufficient replacement

There is a bounded finite-prime projection with exactly the same zero set,
retaining any prescribed initial prime coordinates and the original bound.
`exists_smooth_zero_set_representative_of_bounded_pure` proves this by a
continuous prime-torus lift, two zero-free anchors, and simultaneous disc
contraction. It does not claim equality of multiplicities or finite polynomial
support.

The replacement closes the bounded-constituent question:
`bounded_dirichlet_constituent_ne_zero` excludes every zero of a nonzero bounded
Dirichlet constituent of `ξ`, for arbitrary half-plane boundary `x`.

[Paper proof and Lean declarations](../3-formalized/bounded-pure-dirichlet-series-have-finite-prime-zero-sets.md).
[Closed constituent route](../5-failed/bounded-dirichlet-constituents.md).
