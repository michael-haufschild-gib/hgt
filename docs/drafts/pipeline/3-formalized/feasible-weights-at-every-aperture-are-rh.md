# Feasible weights at every aperture are RH

- **ID:** feasible-apertures-rh
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1011/obstacles-summary.md`, A98.
- **Statement:** RH iff every positive aperture admits a real weight system with nonnegative full Weil form. Equivalently, failure of RH leaves one finite aperture with no feasible weight.

## Proof

A finite nonnegative mixture of compact Weil tests fits inside a common aperture. Choose a feasible weight there. Its Weil sum is nonnegative; if the mixture is prime-blind, all weight terms cancel. The remaining archimedean sum is nonnegative. The unconditional prime-blind criterion gives RH. Conversely, RH makes the von Mangoldt weight feasible at every aperture.

The weights may vary arbitrarily with the aperture. Finite support of the mixtures suffices; no compactness or compatibility of the feasible weight systems is assumed.

## Lean

Module: `formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/FeasibleWeightsAtEveryApertureAreRH.lean`.

- `finite_weilTests_common_aperture`
- `primeBlindPositive_of_feasible_at_every_aperture`
- `riemannHypothesis_iff_feasible_at_every_aperture`
- `not_riemannHypothesis_iff_empty_aperture`

Direct `lake --old env lean` audit passed. Transitive axioms: `propext`, `Classical.choice`, `Quot.sound`. Imported by `ArithmeticOfSquareRootPrecision.lean`.
