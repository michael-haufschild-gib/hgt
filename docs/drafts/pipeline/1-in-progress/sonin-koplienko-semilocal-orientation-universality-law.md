# Sonin Koplienko-semilocal orientation universality law

## Status

In progress — paper proof and Lean formalization complete; literature novelty audit pending.

## Theorem-first provenance

- `RHTower/SoninKoplienkoSecondOrderNoGo.lean`
  - `centralSoninKoplienkoSecondOrderGram_eq_residualEnergy`
- `RHTower/SoninSemilocalMetricLog.lean`
  - `semilocalPrimeLogTailMode_eq_soninCoefficient_phase`
- `RHTower/SoninPrimePowerRegularization.lean`
  - `soninLogPrimePowerCoefficient_ne_zero`
  - `soninPrimePowerTailEnergy_pos`

## Universal law

For every central aperture and retained prime-power Euler coefficient `c`, the Koplienko
second-order Gram remainder is invariant under `c ↦ -c`, but the zero-frequency semilocal
logarithmic tail equals `-2 Re c`. Since the actual coefficient has positive real part, the
quadratic channel identifies the two orientations while the linear channel separates them by a
nonzero sign reversal.

## Lean status

Formalized in
`formal/GaloisForLFunctions/RHTower/SoninKoplienkoSemilocalOrientationUniversalityLaw.lean`.

Exact check:

```text
lake env lean GaloisForLFunctions/RHTower/SoninKoplienkoSemilocalOrientationUniversalityLaw.lean
```

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only.
