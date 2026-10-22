# Mixed power-supported prime-mass finite-window universality law

## Status

In progress — paper proof and Lean source complete; exact check and literature novelty audit pending.

## Theorem-first provenance

- `RHTower/FiniteWindowSeamSincUniversalityLaw.lean`
  - `mixedSteinhausSecondMoment_eq_convolutionDiagonal`
  - `mixedSecondMoment_symmetric_sinc_error_le`
- `RHTower/SquareSupportPrimeMass.lean`
  - `primeMass_le_pow_sum_of_forced`

## Universal law

Whenever the multiplicative convolution of two finite Dirichlet coefficient packets carries a
forced reciprocal-prime mass on the labels `p^m`, the exact mixed Steinhaus second moment carries
that mass through its diagonal. On every deterministic symmetric window, the same lower bound
survives after subtraction of only the explicit convolution off-diagonal sinc energy.

This is the product-carrier version of power-supported mass transference: multiplicative seams do
not require a separate random model or a new window loss term.

## Paper proof

The mixed Steinhaus theorem identifies the random product moment with the squared convolution
diagonal. The power-support lemma lower-bounds that diagonal by the reciprocal prime mass. The
mixed sinc theorem bounds the absolute difference between deterministic and random mixed moments;
its negative half gives the deterministic lower bound.

## Lean status

Source complete in
`formal/GaloisForLFunctions/RHTower/MixedPowerSupportedPrimeMassFiniteWindowUniversalityLaw.lean`.

Exact source check is deferred because the parent
`FiniteWindowSeamSincUniversalityLaw.olean` is not yet present. Source proof is complete; parent
and this file remain in the final dependency-refresh batch.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only; corpus search found
mixed finite-window seam control and single-carrier power-supported prime mass separately, but no
mixed convolution transference theorem.
