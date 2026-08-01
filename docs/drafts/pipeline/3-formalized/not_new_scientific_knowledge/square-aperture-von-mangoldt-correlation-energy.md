# Square-aperture von Mangoldt correlation energy — Lean formalization

- **ID:** `square-aperture-von-mangoldt-correlation-energy`
- **Stage:** `3-formalized`
- **Type:** `[BRIDGE] [EXACT IDENTITY / FORWARD RH IMPLICATION]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Paper proof:**
  `../../2-fully-proven/not_new_scientific_knowledge/square-aperture-von-mangoldt-correlation-energy.md`

## Module

`GaloisForLFunctions.RHTower.CCMSharpPrimeWindowSquareCorrelationEnergy` provides:

- `squareWindowContains`, the square-aperture incidence relation;
- `squareWindowOverlapKernel` and `squareWindowFirstMomentKernel`;
- kernel nonnegativity and symmetry;
- fixed-carrier square-window expansion;
- generic finite quadratic and weighted Fubini identities;
- `squareWindowCorrelationEnergy_eq_centeredDeviation_square_sum`;
- `squareWindowCorrelationEnergy_nonneg`;
- exact square positive-excess comparison;
- `SquarePrimeWindowCorrelationEnergySubpower`, now paper-classified as an exact RH equivalent;
- `riemannHypothesis_of_squarePrimeWindowCorrelationEnergySubpower`.

No theorem asserts the correlation bound. The module proves its exact meaning and downstream RH
consequence unconditionally. The reverse implication is paper-proved from Schoenfeld's
RH-conditional Chebyshev bound and the exact Abel identity, but is not yet formalized because the
project has no formal von Koch--Schoenfeld theorem. The full-square pivot is therefore retired as
an independent source producer; one-sided positive-excess duality is its live successor.

## Audit

- direct module Lean check: pass;
- umbrella import wired;
- targeted module build: pass;
- axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`;
- scoped forbidden-declaration scan and `git diff --check`: pass;
- repository lint reached only three unrelated concurrent umbrella failures:
  `DeningerExteriorFreeness`, `DatumQuotient`, and `SupportReindex`; this module is reachable from
  the `RHTower` umbrella.
