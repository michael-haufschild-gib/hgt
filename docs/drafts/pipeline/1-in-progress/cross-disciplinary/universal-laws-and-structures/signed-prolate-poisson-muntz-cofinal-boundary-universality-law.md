# Signed-Prolate Poisson–Müntz cofinal-boundary universality law

## Status

Law 252; paper proof and exact Lean module audit passed. Literature novelty audit pending.

## Corpus sources

- `RHTower/ConstrainedProlateSignedTrial.lean`
- `RHTower/ConstrainedProlateSignedSpectrum.lean`
- `RHTower/ConstrainedProlatePoissonMuntz.lean`

## Theorem-first derivation

The signed-trial theorem proves that every fixed signed Prolate eigenvalue has square tending to
one as aperture grows. The Poisson–Müntz theorem applies to any two nonzero exact time-band
eigenpairs. The first statement therefore discharges the second theorem's nonzero-eigenvalue input
cofinally for the actual signed spectrum.

## Universal law

For any two fixed signed spectral indices, all sufficiently large positive apertures make both
actual signed Prolate eigenvalues nonzero. At every such aperture and every positive sampling
scale, their canonical two-mode constrained real source satisfies the exact square-root-normalized
Poisson–Müntz Abel boundary law, with the physical endpoint/lattice charge as limit.

## Paper proof

1. Since `σ_n(a)^2 → 1`, the open complement of `{0}` eventually contains each square, hence
   `σ_n(a) ≠ 0` eventually. Intersect this event for the two fixed indices with `a > 0`.
2. Use the unconditional signed eigen-equations for the two modes.
3. Cast each nonzero real signed eigenvalue to a nonzero complex eigenvalue.
4. Apply the canonical two-mode Poisson–Müntz boundary theorem.

No numerical pre-certification applies: conclusion follows from formal convergence and exact
eigen-equations, with no finite numerical threshold asserted.

## Lean target

- Module: `GaloisForLFunctions.RHTower.SignedProlatePoissonMuntzCofinalBoundaryUniversalityLaw`
- Capstone: `RHTower.signedProlate_poissonMuntzCofinalBoundaryUniversality`
- Exact check: `lake env lean GaloisForLFunctions/RHTower/SignedProlatePoissonMuntzCofinalBoundaryUniversalityLaw.lean`

## Novelty

Pending primary-source literature search after corpus discovery reaches exhaustion.
