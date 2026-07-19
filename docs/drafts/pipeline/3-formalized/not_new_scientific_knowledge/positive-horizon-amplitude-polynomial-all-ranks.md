# Positive horizon amplitude polynomial in all ranks

- **ID:** `positive-horizon-amplitude-polynomial-all-ranks`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `HTGeometry/ProjectiveHorizonAllRankQSystem.lean`

## Statement

For every field `F` and all natural ranks `m,n`, the finite positive-coordinate horizon amplitude
polynomial is nonzero. No hypotheses `0 < m` or `0 < n` are required.

## Paper proof

If `m=0`, the defining determinant is the empty determinant, hence the amplitude is `1`. If
`n=0`, the unit-constant coefficient sequence has zeroth coefficient `1`, and the corresponding
Toeplitz determinant is triangular with diagonal `1`, so it is again `1`. If both ranks are
positive, use the existing evaluation certificate: set the coordinate at index `n-1` to `1` and
all other finite coordinates to `0`; the evaluated matrix is triangular with diagonal `1`, so the
polynomial evaluates to `1` and cannot be zero.

## Novelty audit

This is a boundary-rank completion of an existing determinant certificate, not new scientific
knowledge. It closes a false Prop boundary: positivity of both ranks was an artifact of one chosen
evaluation point, not a mathematical condition on nonvanishing.

## Lean certificate

Modules:

- `formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonAllRankQSystem.lean`;
- `formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonPolarizationTower.lean`.

Strengthened declarations:

- `positiveHorizonAmplitudePolynomial_ne_zero`;
- `positiveHorizonAmplitude_ne_zero_of_algebraicIndependent`;
- `hypertranscendentalHorizonAmplitude_ne_zero`;
- `HypertranscendentalPolarizationTower.noncaustic`.

All four are now valid without `0 < m` or `0 < n`.

Validation on 2026-07-19:

- exact source checks of both modules — PASS;
- exact leaf builds of both modules — PASS;
- axiom audit of all four strengthened declarations — only
  `[propext, Classical.choice, Quot.sound]`.

## Gates

- [x] exact corpus and generated API searched
- [x] zero-rank and zero-depth providers identified in the same module
- [x] dependency-closed paper proof
- [x] Lean formalization
- [x] exact leaf build and axiom audit
