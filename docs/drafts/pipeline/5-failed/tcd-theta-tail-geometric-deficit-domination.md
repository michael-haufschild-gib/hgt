# TCD theta-tail geometric–deficit domination

- **ID:** TCD-GDD
- **Stage:** 5-failed
- **Type:** PROVEN STANDALONE-ROUTE NO-GO; POSITIVE SURVIVOR RETAINED
- **Corpus source:** `scripts/formal_tools.py research` results for
  `thetaTailFirstMomentKernel definition nonnegative positive semidefinite factorization convolution`,
  `thetaTailFirstMomentKernel arbitrary packet compact core positivity remaining`, and
  `thetaTailDeficitKernel positive semidefinite no go`.

## Statement

For every finite nonnegative node packet and every real coefficient vector, twice the geometric
quadratic form dominates the negative part of the deficit quadratic form:

`0 ≤ 2 Q_geometric + Q_deficit`.

## Intended RH proof chain and failed link

The intended chain was geometric–deficit domination → positive semidefiniteness of
`thetaTailFirstMomentKernel` → all-plane double-Laplace Bezoutian positivity → corpus theorem
`riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian` → RH.

The first arrow only holds on nonnegative real nodes because
`thetaTailFirstMomentKernel_eq_geometric_add_deficit` requires both nodes nonnegative.  The
double-Laplace identity integrates over all of `ℝ × ℝ`.  Simultaneous reflection recovers the
negative-negative quadrant but not either mixed-sign quadrant.  Therefore the conjecture as
stated does not close the advertised RH chain.

This is the all-order endpoint burden; finite D1 does not imply it.  Corpus theorem
`fixedRank_hankel_not_stieltjes` rules out that generic inference.

## Kill criteria

- A finite nonnegative node packet with `2 Q_geometric + Q_deficit < 0` kills positive-cone
  kernel PSD but does not by itself contradict RH; kernel PSD is stronger than positivity of the
  cofinal exponential double-Laplace family.
- Proving the deficit kernel PSD would be an invalid shortcut: its diagonal vanishes.  The first
  hostile task is to prove strict two-node indefiniteness, forcing a genuine domination theorem.
- Entrywise nonnegativity cannot close the route; arbitrary signed coefficient vectors are required.

## Log

- 2026-08-29 — created from corpus endpoint and geometric–deficit split; frontier map untouched.
- 2026-08-29 — standalone chain retired after auditing the domains in
  `ThetaTailFirstMomentDoubleLaplace`: the endpoint is all-plane, while the split is
  positive-cone only.  `ThetaTailPositiveConeExtensionNoGo` gives a continuous symmetric,
  reflection-invariant, entrywise-positive kernel equal to the rank-one constant kernel on the
  positive cone but with a negative mixed-sign two-node compression.

## Positive survivor

The positive-cone split remains an exact local identity.  Lean proves that its deficit term is
strictly positive off diagonal yet has negative determinant on every distinct two-node packet.
Thus any future source-specific same-sign argument must prove genuine geometric domination.  It
cannot be promoted to the RH endpoint without a separate mixed-sign theorem.  Both statements are
formalized; no standalone RH claim remains.
