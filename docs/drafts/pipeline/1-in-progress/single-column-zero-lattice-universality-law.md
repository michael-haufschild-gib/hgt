# Single-column zero-lattice universality law

## Status

Exact Lean check passed with
`lake env lean GaloisForLFunctions/RHTower/SingleColumnZeroLatticeUniversalityLaw.lean`.

## Lean-generated inputs

- `ColumnRigidity.lean`: a zero of `1 - A b⁻ˢ` has fixed real part
  `log ‖A‖ / log b`.
- `ColumnarInterferential.lean`: every zero caused by one column propagates with vertical period
  `2π / log b`.

## Survivor

The divisor of any nontrivial single Dirichlet column is constrained simultaneously in both
coordinates: one horizontal line and a full vertical arithmetic lattice through every zero. The
law is algebraic/phase-theoretic and needs no analyticity hypothesis.

## Formal target

`GaloisForLFunctions.RHTower.SingleColumnZeroLatticeUniversalityLaw`

## Novelty audit

Pending post-formalization literature search.
