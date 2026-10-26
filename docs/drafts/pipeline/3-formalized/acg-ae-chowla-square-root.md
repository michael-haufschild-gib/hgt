# Successor correlations cancel to the square root almost surely

- **ID:** acg-ae-chowla-2026-10-26
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ArithmeticCorrelationGeometry P4 (successor charge), MC Chowla-type inputs
- **Statement:** For every source bounded by one, at Haar-almost every gauge point, simultaneously
  for all shifts `h ≥ 1`, `Σ_{n≤N} (χa)(n)·conj((χa)(n+h))` and `Σ_{n≤N} (χa)(n)(χa)(n+h)` are
  `O(√N log² N)`; for `μ` this is two-point Chowla at square-root scale on a Haar-full part of the
  orbit; at `x = 0` both are `Σ μ(n)μ(n+h)`.

## Proof
Successor monomials are characters of the distinct ratios `n/(n+h)`; unconjugated ones of the
distinct `n(n+h)`; both orthonormal. Rademacher–Menshov + Borel–Cantelli law
(`ae_exists_norm_orthoSum_le`), countable intersection over shifts.

## Lean
`formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/SuccessorCorrelationsCancelToTheSquareRootAlmostSurely.lean`.

## Insight
Square-root Chowla, like RH, is a typicality statement about the point 0 of the Möbius orbit.
