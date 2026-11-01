# Local Fourier support does not transfer to Weil's dilation correlation

- **Stage:** 5-failed
- **Type:** FALSIFIED — one shortcut inside the two-place programme
- **Rejected claim:** the global `ratCorr` in the p-adically glued state admits a
  p-adically continuous realization at the identity.
- **Killing theorems:** `not_padic_continuous_ratCorr` at every prime, and
  `not_padic_continuous_ratCorr_twoPrimeUnits` already on any fixed two-prime
  slope group away from that prime.
- **Strongest positive survivor:** every principal-unit resolution inside a fixed
  two-prime slope group retains the full negative and mass-zero Weil indices,
  every global correlation value by approximation, and uniform positive oscillation.
  Already translations in `ℤ[1/(qr)]`, all of p-adic norm at most one, retain
  the full affine index `κ(ratCorr)+1`. The two shifts `0,1` supply the extra square.
- **Simultaneous-place boundary:** for finite support `S` and selected places `T`,
  the actual principal S-unit group loses exactly the coordinates in `S∩T`.
  Zero free primes give only one, one gives a nonzero logarithmic lattice,
  and at least two give density with full Weil indices and a uniform positive
  correlation oscillation across all finite resolutions. The exact classification
  is [paper-proved and Lean-certified](../3-formalized/principal-s-unit-logarithmic-support-boundary.md),
  with five clean transitive axiom audits.
- **New insight:** gluing the successor at a finite place retains the archimedean
  correlation at every local resolution. Compact support of local Fourier test
  functions does not provide the missing continuity of that correlation.
- **Paper and Lean status:** [local theorem](../3-formalized/every-padic-neighborhood-carries-the-whole-weil-index.md),
  [fixed-prime core](../3-formalized/three-prime-principal-unit-core.md),
  [bounded affine core](../3-formalized/two-prime-affine-core-with-bounded-translations.md);
  direct module checks pass; only `propext`, `Classical.choice`, `Quot.sound`.
- **Scope:** the global two-place comparison remains open. Finite-idèle and S-unit
  constructions impose additional valuation conditions and are not retired here.
