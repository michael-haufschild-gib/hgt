# Matrix principal-symbol spectral/differential universality law

## Status

Fully proven on paper; formalized in Lean 4; **verification gate passed**.

`lake build` succeeds on the module inside the `GaloisForLFunctions.HTGeometry` umbrella (which imports it), and `#print axioms` gives exactly `propext, Classical.choice, Quot.sound` for

```text
GaloisForLFunctions.HTGeometry.matrixPrincipalLowerLaw_spectralDifferentialHorizon
```


## Theorem-first source

- `matrixDifferentialDependentSet_eq_firstSingularSet_of_flat`: a realized flat matrix principal
  law with one regular direction has exact differential-dependence locus equal to its first
  determinant horizon.
- `matrixPrincipalSpectralPolynomial_eq_first`: every normalized characteristic polynomial of
  the same flat symbol tower is independent of filtration depth.
- `Matrix.eval_charpoly`: evaluating the characteristic polynomial at zero gives the determinant
  of the negative matrix.

The corpus proved determinant-horizon collapse and full spectral conservation in disjoint terminal
modules.  No theorem identified the actual differential-algebraic phase boundary with the zero
root of the conserved first-layer spectral polynomial.

## Universal law

For every finite-rank flat realized matrix principal law with an algebraically free source and one
regular direction, the full normalized characteristic polynomial is conserved at every jet layer.
A law direction is differentially algebraically dependent exactly when zero is a root of the
single normalized characteristic polynomial at layer zero.

## Paper proof

Flat differential-horizon collapse identifies the dependence locus with
`det(symbol 0 A) = 0`.  Spectral holography identifies every normalized layer polynomial with
the layer-zero polynomial.  At the regular reference direction, left normalization multiplies
`symbol 0 A` by an invertible matrix, so it preserves determinant vanishing.  Evaluation of the
normalized characteristic polynomial at zero is the determinant of its negative; the additional
sign is nonzero.  Therefore its zero-root condition is equivalent to the first determinant
horizon, hence to actual differential dependence.

## Lean formalization

- Module:
  `GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolSpectralDifferentialUniversalityLaw`
- Theorem:
  `GaloisForLFunctions.HTGeometry.matrixPrincipalLowerLaw_spectralDifferentialHorizon`
- Exact check:
  `lake env lean GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolSpectralDifferentialUniversalityLaw.lean`
  passed on 2026-07-22.

## Novelty audit

Pending literature audit after theorem-generation phase. Corpus audit is negative.
