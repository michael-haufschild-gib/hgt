# Explicit infinite square-rate reader symbol

- **ID:** xi-theta-square-rate-reader-symbol
- **Stage:** 3-formalized
- **Type:** BRIDGE THEOREM (Lean), [PROVED]
- **Date:** 2026-07-10
- **Module:** GaloisForLFunctions.RHTower.XiThetaSquareRateReader
- **Paper proof:** ../../2-fully-proven/new/xi-theta-square-rate-reader-symbol.md

## Formal surface

- `sqrt_thetaSquare`: the principal complex square root returns the positive integer at `n^2`.
- `thetaSquareBlaschkeSymbol`: the explicit sine/sinh square-zero quotient.
- `thetaSquareBlaschkeSymbol_zero`: every square is a zero of the quotient.
- `thetaSquareBlaschkeNodeSlope`: the explicit node derivative.
- `hasDerivAt_thetaSquareBlaschkeSymbol`: the node derivative formula.
- `thetaSquareBlaschkeNodeSlope_ne_zero`: every positive node is simple.
- `thetaSquareBlaschkeReaderSymbol`: inverse-slope normalization of the removable difference quotient.
- `thetaSquareBlaschkeReaderSymbol_self`: selected-square value one.
- `thetaSquareBlaschkeReaderSymbol_other`: every other square is annihilated, without a cutoff.
- `thetaHeatRateReaderSymbol_self` and `thetaHeatRateReaderSymbol_other`: the same interpolation in
  the physical heat-rate variable `pi m^2`.

## Certificate

- Direct source check passed.
- Targeted build passed: `lake build GaloisForLFunctions.RHTower.XiThetaSquareRateReader`
  (8601 jobs).
- Axiom audit passed for the derivative, dimensionless interpolation, and physical-rate
  interpolation theorems; only `propext`, `Classical.choice`, and `Quot.sound` occur.
- Generated theorem API refreshed; formal lint passed.
- No full or umbrella build.
- No sorry, admit, axiom, opaque, or unsafe declaration.

## Scope

The module constructs and normalizes the exact infinite interpolation symbol. It does not yet
formalize right-half-plane Hardy membership, its exact boundary norm, or the Paley-Wiener L2
representative.
