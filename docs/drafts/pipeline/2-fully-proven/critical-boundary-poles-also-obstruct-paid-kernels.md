# Critical-boundary poles also obstruct paid kernels

- **ID:** critical-boundary-paid-kernel-obstruction
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean pending)
- **Source:** Q-III; the cleared Möbius Mellin identity and the paid-energy Mellin bound.
- **Statement:** A translated zeta pole on `Re s = 1/2` with strictly positive uncancelled order forces every paid critical Wiener kernel to vanish at that boundary point.

## Goal

Audit the boundary omitted by the existing strict-interior translated-zero
hull. This constrains the actual paid ideal. It does not identify which
points occur in any unshifted common Gram module, nor assert existence of a
zeta zero in this position.

## Gates

- [x] 0 → 1: source fixed, exact boundary and analytic inputs identified.
- [x] 1 → 2: complete paper proof and novelty audit.
- [ ] 2 → 3: leaf `lake --old env lean` checks and transitive axiom audit.
- [ ] 3 → 4: publication audit.

## Approach

Let `s0 = rho - epsilon`, `Re s0 = 1/2`, `0 < epsilon < 1/2`,
`Re rho < 1`. For a real paid kernel the cleared identity is

`Z_epsilon(s) (Phi(s) + m zeta(s)) = (s+epsilon-1) zeta(s) K(s)`.

The paid prefix has bounded pronic energy. The corpus supplies
`norm_cmellinCell_le` and `abs_tsum_mul_mellinCell_le`, hence along
`s=s0+u`, `u>0`, the actual Mellin pairing satisfies
`|Phi(s0+u)| = O(u^(-1/2))`. This uses generic prefix energy, not a
half-damped coefficient bound. The current existential cleared-continuation
helper must retain its identification with that actual Mellin pairing.

If `ord_rho zeta = a` and `ord_s0 zeta = b`, with `a>b`, factor both
analytic zeta germs and divide the identity by `u^b`. Its left side is
`O(u^(a-b-1/2))`, which tends to zero. The right side tends to a nonzero
constant times `K(s0)`. Critical Wiener evaluation is continuous on the
closed half-plane, so `K(s0)=0`. Real and imaginary parts give the complex
paid-ideal statement and the boundary Bohr obstruction.

No kernel jet conclusion follows from this argument: a critical Wiener
series need not extend analytically across the boundary.

## Corpus and novelty audit

Searches recorded in `/tmp/qiii-paid-critical-zero-novelty.json` and
`/tmp/qiii-receiver-endpoint-novelty.json` find existing strict-interior
zero propagation and the exact infimum damping-width law. Those statements
do not decide payment at an attained boundary zero.

Relevant checked source statements:

- `APaidReceiverContinuesTheDirichletSeriesAcrossItsAbscissa` constructs
  the actual complex Mellin continuation from generic paid prefix energy.
- `FiniteKernelsRepairAPositiveDriftOnlyAtItsPole` bounds the real Mellin
  pairing by `sqrt E * sqrt(2 sigma^2 (1+1/(2 sigma-1)))`.
- `TheHalfDampedReceiverIsTheBoundaryEnergyOfItsDirichletSeries` bounds
  a complex cell by `norm s / Re s` times the corresponding real cell;
  this cell estimate itself has no half-damped coefficient premise.
- `TheHalfDampedHyperplaneLawHasAnExactLogarithmicThreshold` has the
  stronger real-axis little-oh paid Mellin bound; the big-oh bound already
  suffices for integral positive pole order.

## Status

Analytic proof outline established. Exact complex bound, boundary continuity,
finite zeta-order factorizations, and boundary specialization still require
Lean verification. The strict-interior order/jet refinement is independently
being checked. No canonical source theorem changed for this candidate.

## Closed paper argument and source audit

All analytic inputs are now identified in existing checked sources:
`PrimeShiftResidueClosability.analyticOrderAt_riemannZeta_ne_top` proves
finite order away from one; `WeilBoundaryDilation.continuousOn_LSeries_half`
proves continuity of every half-plane absolutely summable Dirichlet series
on the closed critical half-plane. Neither carries an unproved source premise.
The latter applies directly to the critical Wiener kernel.

The generic energy bound gives the sharper explicit estimate

`|u Phi(s0+u)|^2 <= |s0+u|^2 E (2*u^2+u)`,

so `u Phi(s0+u)->0`. Adding the bounded analytic term `m*zeta` preserves
this limit. Near s0, the factor s+epsilon-1 is nonzero, so the cleared
identity reduces to

`zeta(s+epsilon)*(Phi(s)+m*zeta(s)) = zeta(s)*K(s)`.

Both zeta germs have finite orders a>b. Write them as
`(s-s0)^a*g(s)` and `(s-s0)^b*h(s)`, with g,h analytic and h(s0)!=0.
For s=s0+u and u>0 cancel u^b. The left side becomes
`u^(a-b-1)*g(s0+u)*[u*(Phi(s0+u)+m*zeta(s0+u))]`, which tends to zero.
The right side tends to `h(s0)*K(s0)` by closed-half-plane continuity.
Thus K(s0)=0. Apply this to both real parts of a complex paid kernel to
obtain the Bohr hull statement. Nonempty obstruction hull implies nonpayment
by the existing paid-ideal theorem. No existence of such a zeta point is
presumed; the source implication is proved for the complete actual ideal.

This is an endpoint application of ordinary analytic factorization and the
paid-energy Mellin estimate. No new general removable-singularity principle
is claimed. Kernel jets at the boundary remain outside the conclusion.

The assembled `/tmp/qiii-critical-boundary-pole-check.lean` contains the
explicit cleared identity, paid Mellin bound and rate, generic order-loss
cancellation, and actual real/complex paid-kernel applications. All new
boundary pieces remain unverified. This replaces the two smaller Mellin
checks in the prepared next queue; do not start it before session `32035`
finishes.
