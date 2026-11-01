# Positive moment cancellation on an actual two-prime cone

- **Stage:** 1-in-progress; conjectural construction, not a zeta counterexample.
- **Parent:** SC2 in `route-sc-complete-family-and-coupling.md`.
- **Question:** Do polynomial weight lower bounds, tempered height counts and joint two-prime phase separation exclude cone cancellation?

## Proposed realization

For distinct primes `p,q` and `0<d<D<1/2`, construct distinct
`z_j=delta_j+i gamma_j`, with `d<=delta_j<D`, and positive weights `w_j`, such that

1. `sup delta_j=D`, with no maximum; only finitely many `|gamma_j|<=T`.
2. `sum_j w_j<infinity` and `w_j>=(1+|gamma_j|)^(-8)`.
3. For every `(a,b)` in `N^2` except `(0,0)`,
   `sum_j w_j exp((a log p+b log q)z_j)=0`.

The joint clock relation is exact, so the existing two-prime separation theorem
applies. Weights are freely chosen positive masses, not the spline weights of
zeta. A construction would therefore obstruct that proposed package of generic
inputs while leaving the actual SC2 implication open.

## Finite correction mechanism

Let `lambda_(a,b)=a log p+b log q`. At a new real level `delta`, normalize
each old residual moment by `exp(-delta lambda_(a,b))`. A finite set of such
residuals `r_(a,b)` is corrected by the torus density

`A - 2 Re sum_(a,b) r_(a,b) exp(-i(a theta_1+b theta_2))`,

with `A>2 sum |r_(a,b)|`. Orthogonality gives precisely the desired negative
moments. Density of the actual two-prime phase orbit should replace this strictly
positive density by a finite positive quadrature on that orbit, preserving all
selected moments and total mass. Strict positivity gives a stable finite
quadrature; its nodes can then be chosen at arbitrarily large heights while
keeping its weights bounded below.

## Infinite correction mechanism

Use levels `delta_k` increasing to `D` and cancel all frequencies below `L_k`.
If the preceding moments below `L_(k-1)` vanish and preceding total mass is `M`,
the next normalized residual has absolute sum at most

`M sum_(lambda>L_(k-1)) exp(-(delta_k-delta_(k-1)) lambda)`.

This tail is summable and can be made arbitrarily small by the preceding
cutoff. Choose cutoffs so correction masses are summable. At each fixed
frequency, finite-prefix cancellation and the mass tail then give exact zero.
Choose each finite quadrature beyond all earlier heights and beyond the bound
needed for its positive weights to dominate `(1+|gamma|)^(-8)`.

## Unproved obligations

- Stable exact positive quadrature on an arbitrarily late part of the actual
  two-prime orbit, with a weight lower bound independent of how late it is placed.
- A non-circular schedule of levels, cutoffs and correction masses.
- Lean formalization of the resulting joint moment realization.

Matching the additional upper bound `w_j<=C(1+|gamma_j|)^(-8)` requires a
quantitative orbit-covering estimate and is not claimed by this construction.
