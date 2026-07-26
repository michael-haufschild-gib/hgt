# Bourgain exact-curve estimate on a whole pulled-back period cell

- **Status:** RETIRED AS A ROUTE TO SHARP `A₆`
- **Date:** 2026-07-25
- **Parent:** `bourgain-zeta-subconvexity-13-84`

## Attempt

Pull each pair of exact square-root-curve blocks through the osculating
coordinate map, cover by full parabola period cells of phase volume `M⁶`,
and compare the exact sums additively with their quadratic Taylor models on
every entire pulled-back cell.

## Obstruction

The inverse osculating map and inverse anisotropic dilation make a whole
pulled-back period cell much longer than Bourgain's original physical
localization region. The available pointwise Taylor estimate contains
`R·(M/N)³`, where `R` is that inverse-cell radius. Its scale growth is too
large to absorb into the quadratic main term. Covering a coordinate bounding
box also loses the two linear periodic averages. Thus the route cannot
produce the source estimate `N^(4+ε)M²`.

This is structural, not a missing constant: Bourgain's proof first localizes
on the physical domain, treats the Taylor remainder as a bounded smooth
Fourier multiplier, and uses periodic averaging plus two scale reductions.
It does not extend the exact curve uniformly over a whole skew period cell.

## Positive survivor

The geometry and main term remain useful and are fully formalized:

- exact physical `A₆` normalization with Jacobian `N⁶`;
- exact `K×M` block partition and exact-local-sum identification;
- sharp phase-cell volume `M⁶`;
- base separation `sqrt(q₂/N)-sqrt(q₁/N) ≥ M/(2N)`;
- combined determinant lower bound `(3/512)(M/N)^10`;
- reciprocal Jacobian bound `(512/3)(N/M)^10`;
- one-cell quadratic main term
  `≪ C² N^10 M^(2+ε)`, hence normalized scale
  `N^(4+ε)M²`.

Lean status: `[LEAN-PROVED]` in
`BourgainParabolaFundamentalCell.lean`,
`BourgainAnisotropicFundamentalCell.lean`,
`BourgainA6PhysicalBox.lean`, and
`BourgainA6BlockLocalization.lean`.

## Replacement route

Formalize Bourgain equations (2.4)--(2.10) in their actual order:
physical-cube localization, periodic averaging in the two linear variables,
bounded-multiplier Taylor replacement, planar `L⁶` decoupling, and the second
scale reduction. Then rescale (2.10) to (2.23) and use the already-formalized
separated linear-to-bilinear recurrence.
