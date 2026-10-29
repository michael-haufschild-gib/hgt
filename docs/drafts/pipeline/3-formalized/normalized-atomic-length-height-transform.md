# Normalized atomic length-height transform

- **ID:** normalized-atomic-length-height-transform
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-2910/fable2.md`, §1.3.
- **Statement:** For the positive Fourier convention, raw atoms of width `w` have transform
  `w hφ(wz) Σ_(n≤N)x_n exp(iz log n)`. Unit-mass dilation at height `T=1/w` removes `w`.

## Exact dictionary

The conventional Dirichlet polynomial has coefficients `a_n=√n x_n` and argument `1/2-iz`.
These identities hold at every complex `z`, so they retain off-line zeros and polar arguments.
A continuous compact profile of nonzero integral has nonzero transform values above every
real height; `T` is a decay scale, never a hard cutoff.

## Paper proof

Translation by `log n` contributes `exp(iz log n)`. Changing variables `u=wv` contributes
the Jacobian `w`; multiplying the dilated profile by `1/w` cancels it.
The identity `√n=exp(log n/2)` converts the polynomial to the stated critical-line convention.
The compact-profile transform is entire and nonzero at zero. If it vanished on a real tail,
the identity theorem would force it to vanish everywhere, contradicting the nonzero integral.

## Lean anchors and validation

Module: `formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheNormalizedAtomicTransform.lean`.

- `paperFT_atomicTest_atomDilate`
- `dirichletPoly_eq_mellinPolynomial`
- `paperFT_atomicTest_at_height`
- `exists_paperFT_ne_zero_above`

Direct `lake --old env lean` check passed. All four transitive audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. SSHA umbrella import added.
