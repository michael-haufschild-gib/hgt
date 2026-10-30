# Replacement errors vanish uniformly on bounded overlap

- **ID:** replacement-errors-vanish-uniformly-on-bounded-overlap
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** one-horizon-makes-every-bounded-overlap-positive

## Statement

For every nonzero compact `C²` unit profile and fixed positive conductor,
the complete self, center, two-pole, and separated cross residuals vanish
uniformly in normalized norm for `0<c≤K`.

## Proof [PROVED HERE]

Once `N≥K`, the exact self remainder is at most `exp(1/2)K/(2N)`.
The normalized Ramanujan vectors have bounded norm. The center residual
is exactly `c` times its residual at `c=1`, so its norm is bounded by `K`
times a sequence tending to zero.

Put `A=Σ_{j<m}|u_m(j)|`. The exact pole moment bound and the two-pole row
estimate give squared unnormalized norm at most
`4 C_pole² A² c⁴≤4 C_pole² A² K⁴`. On separated pairs the already proved
cross-entry bound has coefficient `152(∫|φ|)²(c/N)²/∫φ²`. The reciprocal
square kernel estimate gives squared unnormalized norm at most
`(36 C_cross A c²)²≤(36 C_cross A K²)²`.
Dividing these fixed bounds by `log N` proves both remaining norm limits.
No overlap-dependent threshold remains.

## Lean formalization

`CriticalArithmeticCorrelationTheory/TheReplacementErrorsVanishUniformlyOnBoundedOverlap.lean`:

- `eventually_fullWeilPoleError_norm_uniform_overlap`
- `eventually_separatedCrossError_norm_uniform_overlap`
- `eventually_completeWeilSelfError_norm_uniform_overlap`
- `eventually_fullWeilCenter_norm_uniform_overlap`

Direct Lean audit passed. All four transitive axiom audits contain only
`propext`, `Classical.choice`, `Quot.sound`. Supporting operator estimate;
no separate contribution count.
