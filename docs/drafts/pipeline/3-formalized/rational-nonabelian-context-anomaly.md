# Rational non-Abelian context anomalies at every order

Stage: 3-formalized

Status: `[PAPER-PROVED] [LEAN PROVED] [STRENGTHENED]`

Source: Theorem 6.3 and the context-order construction of *Locally Quantum, Globally
Non-Hilbertizable* (Zenodo 21982163).

## Exact claim

For every `r`, an explicit rational kernel on `r+4` contexts with three internal directions per
context has all of the following properties simultaneously:

1. every maximal proper context restriction is positive semidefinite;
2. the full kernel is not positive semidefinite;
3. one principal two-direction sector is itself a positive semidefinite Gram kernel; and
4. two triangle Wilson products in that same principal sector have nonzero commutator.

The construction is a `1 ⊕ 2` direct sum. The scalar direction carries the balanced all-order
globality obstruction. The two-dimensional direction is a rational Gram sector in a fixed
four-dimensional ambient space and carries the noncommuting loop data. The principal-sector
identity is part of the headline theorem, so the obstruction and curvature are not unrelated
existence claims.

## Strength over source proof method

The source proves a two-dimensional existence theorem using unitary phases and a small-parameter
continuity argument. The formal theorem uses internal dimension three, but replaces perturbation
and transcendental phase choices by one exact rational construction valid at every order. It is
therefore stronger in arithmetic exactness and proof uniformity, but not in minimal internal
dimension. No claim of a formalized two-dimensional construction is made.

## Lean status

`formal/GaloisForLFunctions/HTGeometry/RationalNonabelianContextAnomaly.lean`, headline declaration
`exists_rational_nonabelian_context_anomaly`. The statement is universal in `r`, has no external
premises, and introduces no axioms. Supporting exact laws include
`contextBlockSum_posSemidef_iff`, `rationalNonabelianContextAnomaly_wilsonSector`, and
`rationalWilsonLoops_commutator_ne_zero`.
