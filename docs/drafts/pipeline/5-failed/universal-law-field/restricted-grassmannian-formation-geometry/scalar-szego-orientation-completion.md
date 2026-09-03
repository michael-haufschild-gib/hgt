# Scalar Szegő orientation completion — retired

- **ID:** ULF-SSOC-001
- **Stage:** 5-failed
- **Killed class:** scalar causal outer completion claimed to preserve the unsquared
  reflection-odd prime current.

## Proposal

After the unique `pi exp(2|x|)` anomaly subtraction of `ULF-UASA-001`, choose the scalar Szegő
outer factor with squared boundary modulus equal to the residual prime--theta modular density and
identify its boundary value with the signed source half-density.

## Killing theorem

The signed half-density is a nonconstant real odd `L2` function.  Any scalar `H2` function with
real boundary values almost everywhere is constant.  Hence no scalar causal Hardy function has
the required boundary amplitude.

Changing outer phase does not repair this: all scalar outer factors with the same modulus differ
only by a constant unit phase, while the missing datum changes sign under source reflection.

## Strongest positive survivor

The scalar metric leg is canonical and nontrivial: its outer multiplier is zero-free, injective,
and has dense nonclosed range.  Exact orientation requires both Hardy frequency halves; after FE
doubling this agrees with the corpus's minimal four-leg/Krein carrier.  The scalar route is closed,
but the unique metric anomaly survives unchanged.

## Status

Killing theorem and positive survivor are dependency-closed on paper in `ULF-UASA-001`.  Lean
formalization pending; no Lean changes were made in this research phase.
