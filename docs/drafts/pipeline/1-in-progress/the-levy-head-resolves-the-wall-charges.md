# The Lévy head resolves the wall charges

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** ECS Q9; exact head coordinates and left asymptotics, also supporting Q2 contour bounds.
- **Statement:** For every actual energy-domain profile and `Re p < 1/2`,
  `JF(p) = Σ(k≥0) LF(2k+1/2)/(2k+1/2-p)`, absolutely convergently.

## Mathematical connection

`RHTower.ArchimedeanAnomaly.hasSum_archLevyDensity` resolves the Lévy density into
`exp(-(2k+1/2)x)`. Swapping the head integral with one exponential mode should give
`LF(λ)/(λ-p)`. Existing head domination supplies absolute integration; square mass
controls the positive-real transform samples.

The `k=0` term cancels `LF(1/2)/(p-1/2)` in `leftRemainder`. Thus left of the strip,
`-a LF(w)` should equal the remaining archimedean modes, prime heads and the single
charge `LF(-1/2)/(w+17/2)`. This is an exact state identity, not an exclusion claim.

## Proof obligations

1. Exponential-mode Fubini identity on the full energy domain, without trace assumptions.
2. Absolute resolvent summability and equality with the actual head term.
3. Exact charge cancellation in `stateMeromorphic_eq_left`.
4. Uniform decay as the real part tends left; no pointwise values of the profile assumed.

No result counted before Lean formalization. No external novelty or axiom checks.
