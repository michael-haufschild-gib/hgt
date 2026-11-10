# The centred Gaussian current is carried by short cofactors

- **Obstacle:** B13.
- **Stage:** 1-in-progress
- **Type:** CONJECTURE

## Target

Extend the spacing-preserving Vaughan reduction from quadratic cutoffs to
cutoffs growing as powers of the physical Gaussian scale. Then bound the
filtered cofactor tail independently, leaving a genuinely unbalanced
arithmetic core.

For `0≤σ<1`, `β≥σ`, `0<η≤1/2`, fixed degree `d`, and the interior
damping sector, conjecture

`|filtered (M₁−P₁−C_UV)| ≪ h^d t^(d+2)(UV)² X^(−1−σ+η)`

uniformly for `X≥2e UV`, `U,V≥1`, and `0≤h≤1`. Thus
`(UV)² t^(d+3)≤X^(1+σ−η)` makes the normalized error `O(1/t)`.
Taking `V` polynomial in height permits `U` almost as large as
`X^((1+σ)/2)`, unlike the earlier quadratic individual cutoffs.

The remaining type-II convolution should be truncatable to cofactors
`m≤X^(1+δ)/U` with arbitrarily strong power savings, while retaining `h^d`.
This would localize the arithmetic problem to cofactors of size almost
`X^((1−σ)/2)`. The bound for that core remains open.

## Mechanism

The explicit three-term error is at most

`(8+2Dσ+Cσ)t²(UV)²X^(−1−σ)(1+log X)`

when `UV≤X`. The head is absorbed because `U≤X` and `σ<1`.
The inequality `1+log X≤(1+1/η)X^η` removes the logarithm.
The proved half-strip geometry and Cauchy filter bound then retain `h^d`
without any individual quadratic cutoff restriction.

For the cofactor tail, `d>U` and `m>W` force `dm>UW`.
Polynomial coefficient bounds and arbitrary Gaussian moments give a tail
of order `X^(3+2k)/(UW)^(2k)`. A stronger real Mellin twist makes this
bound uniform on the entire forward half-strip. Shifting every polynomial
root back compensates the extra twist exactly and retains every spacing
factor. Choosing `UW≥X^(1+δ)` and large fixed `k` makes the tail negligible.

## Proved cutoff extension

The product-cutoff estimate and its literal filtered application are now
formalized in `GaussianVaughanCutoffHorizon.lean`; all four axiom audits
are clean. The explicit filter constant is
`exp(β+4)(8+2Dσ+Cσ)(1+1/η)16^d dampingFilterCost(ws)`.
See `../3-formalized/b13-power-sized-vaughan-cutoffs.md`.

## Obligations

Prove the actual restricted convolution coefficient and support bounds,
the Gaussian moment tail estimate, holomorphy, and the root-shift identity.
No zero-location or unproved arithmetic-cancellation premise is allowed.
