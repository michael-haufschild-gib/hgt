# Möbius critical soft-hard Fisher boundary universality law

## Status

In progress — paper proof and Lean formalization complete; literature novelty audit pending.

## Theorem-first provenance

- `RHTower/MobiusCriticalFisherTangentCoefficients.lean`
  - `tendsto_infiniteMobiusCriticalFisherTangentDampedCoefficient`
- `RHTower/MobiusCriticalFisherCutoffLimits.lean`
  - `tendsto_squarefreeMobiusCriticalFisherCutoffWardLimit_div_two_mul`

The first terminal module computes the positive-damping critical Fisher coefficient as
`2u / (1 + u)^2`. The second independently computes the hard-cutoff commutator Ward profile and
its one-sided normalization by `2u`.

## Universal law

After taking the Euler critical boundary, hard cutoff and soft damping have a canonical relative
normalization. As the positive clock window vanishes, hard commutator energy divided by the actual
soft damped Fisher coefficient tends to `4`. This ratio is not stated in either source module.

## Lean status

Formalized in
`formal/GaloisForLFunctions/RHTower/MobiusCriticalSoftHardFisherBoundaryUniversalityLaw.lean`.

Exact check:

```text
lake env lean GaloisForLFunctions/RHTower/MobiusCriticalSoftHardFisherBoundaryUniversalityLaw.lean
```

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only.

