# Contracting filters preserve the centred Vaughan error

- **Obstacle:** B13.
- **Stage:** 1-in-progress
- **Type:** CONJECTURE

## Target

Retain the full spacing factor in the difference between the literal
pole-subtracted first-moment prime filter and the same filter applied to
`gaussianCentredVaughanCurrent`.

For a fixed degree `d` filter with roots `exp(hω_j)`, conjecture an actual
arithmetic error `O(h^d t^(d+7)/X)`, uniformly for `0≤h≤1`,
`1≤U,V≤t²`, and sufficiently interior boundary-sector damping at scale
`X≥C_d t⁸`. No hypothesis on the zeros or an unproved arithmetic estimate
is allowed. In particular `X≥C_d t^(d+8)` would give `O(h^d/t)`.

## Verified first estimate

`norm_gaussianPrimeMoment_sub_centredVaughan_le_scale` now proves
`|(M−P)−C_UV|≤(8Dσ+3Cσ+8)t⁷/X` under the preceding unfiltered
sector conditions, `1≤U,V≤t²` and `X≥t⁸`. Its direct source check and
all five transitive axiom audits pass. The earlier `O(1/t)` theorem is
now a corollary of this stronger bound.

## Mechanism

Strengthen the proved unfiltered bound to `O(t⁷/X)` using its explicit
three-term error. The error is holomorphic in complex damping on the
right half-plane. In logarithmic damping coordinates the boundary sector
has complex width comparable to `1/t`. Cauchy's estimate then makes each
twisted finite difference cost `O(ht)`, with constants depending on the
fixed roots and degree. The geometric grid decreases damping, so its
physical scales grow rather than shrink.

## Obligations

Prove holomorphy for the actual infinite arithmetic sums and logarithmic
continuum term. Prove a finite-filter estimate retaining every factor
`h`. Match the recursive difference operator to the actual polynomial
sample weights. Check sector margins and all sampling scales explicitly.

## Scope

This would remove the loss of `h^d` in the current reduction. It would
still leave the independent upper bound for centred type II open.


## Analytic geometry

Use `f(z)=exp((σ+it−β)z) E(ε exp(−2z))`, with `β≥σ` and
`2α≤ξ≤αt`. On a half-strip `Re z>−r`, `|Im z|<r`, `r≈1/t`,
rotation changes `ε` by at most a fixed fraction of `α`. Its real part
stays positive and the enlarged sector remains valid. The physical scale
is comparable to `X exp(Re z)`. Thus `f` is bounded throughout this
half-strip by `O(t⁷/X)`; its bound does not grow under positive real shifts.

A twisted difference `f(z+h)−exp(hω)f(z)` is bounded on the half-width
half-strip by `h M(4/r+|ω|exp|ω|)`. Cauchy's derivative estimate controls
the ordinary difference; the exponential chord controls the twist.
Iterate through shrinking half-strips. Their positive real translation
invariance avoids a right-endpoint loss, and supplies the full `h^d`.
