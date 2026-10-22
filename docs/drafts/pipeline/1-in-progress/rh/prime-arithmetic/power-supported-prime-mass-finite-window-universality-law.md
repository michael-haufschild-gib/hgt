# Power-supported prime-mass finite-window universality law

## Status

In progress — paper proof and Lean formalization complete; literature novelty audit pending.

## Theorem-first provenance

- `RHTower/SquareSupportPrimeMass.lean`
  - `primeMass_le_pow_sum_of_forced`
- `RHTower/SteinhausModel.lean`
  - `integral_normSq_dpoly`
- `RHTower/DirichletPolynomialSincEnergy.lean`
  - `secondMoment_symmetric_sinc_error_le`

## Universal law

For every nonzero dilation rung `m`, any finite positive-index coefficient family containing the
`m`-th powers of a prime family with amplitude at least `δ p⁻¹ᐟ²` carries `δ² Σp⁻¹` in its exact
Steinhaus second moment. On every deterministic symmetric window, the same forced mass survives
after subtracting only the explicit sinc off-diagonal collision energy. Thus randomization loses no
forced prime content, while finite observation localizes its entire possible loss to multiplicative
near-collisions.

## Lean status

Formalized in
`formal/GaloisForLFunctions/RHTower/PowerSupportedPrimeMassFiniteWindowUniversalityLaw.lean`.

Exact check:

```text
lake env lean GaloisForLFunctions/RHTower/PowerSupportedPrimeMassFiniteWindowUniversalityLaw.lean
```

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only.
