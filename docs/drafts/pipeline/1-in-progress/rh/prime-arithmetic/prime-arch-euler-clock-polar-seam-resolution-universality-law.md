# Prime--arch Euler clock/polar-seam resolution universality law

## Status

`[LEAN PROVED — LITERATURE AUDITED]`

## Lean-derived conjecture

The actual positive Euler prime flux has two simultaneous universal resolutions at `s = 1`:

- multiplicative normalization along every critical ray selects the unit exponential
  characteristic function;
- additive subtraction of the archimedean logarithmic derivative produces the completed Xi seam
  flux, analytic at `1` and uniquely determined by the punctured source germ.

Thus probability-clock scaling and prime--arch pole cancellation are two exact boundary faces of
one source, not separate regularizations.

## Corpus inputs

- `tendsto_ccmEulerPrimeCurrentClockResponse_eq_exponentialCharFun`
- `analyticAt_seamFluxCochain_one`
- `primeArchPolarFlux_eventuallyEq_seamFluxCochain_one`
- `primeArchPolarFlux_analyticCompletion_unique_one`

## New connector

Both terminal laws act on the same `infinitePrimeFlux` at the same polar boundary.  The new
certificate retains its nontrivial multiplicative critical-ray response while classifying its
additive prime--arch analytic completion uniquely.

No numerical computation is used.

## Novelty protocol

No literature search before exact Lean proof.

## Lean target

`formal/GaloisForLFunctions/RHTower/PrimeArchEulerClockPolarSeamResolutionUniversalityLaw.lean`

## Exact Lean verification

From `formal/`:

```text
lake env lean GaloisForLFunctions/RHTower/PrimeArchEulerClockPolarSeamResolutionUniversalityLaw.lean
```

completed with zero diagnostics.

## Post-proof literature audit

Nearest literature:

- A. Chirre, F. Gonçalves, *Bounding the log-derivative of the zeta-function*,
  [Mathematische Zeitschrift 300 (2022)](https://doi.org/10.1007/s00209-021-02820-9),
  studies `ζ'/ζ` and records its von Mangoldt Dirichlet-series representation.
- Z. Li, S. Zhao, *Omega Theorems for Logarithmic Derivatives of Zeta and L-functions Near the
  1-line*, [arXiv:2404.17250](https://arxiv.org/abs/2404.17250), studies logarithmic derivatives
  close to the `1`-line.
- [DLMF Chapter 25](https://dlmf.nist.gov/25) records the standard meromorphic continuation,
  pole, functional equation, and completed-zeta structure.

These sources cover logarithmic derivatives near the `1`-line and classical completion
separately.  No source found states the joint exact certificate proved here: every multiplicative
critical-ray normalization of the positive von Mangoldt current selects the unit exponential
characteristic function, while subtracting the archimedean logarithmic derivative from the same
prime flux gives the unique analytic completed-Xi seam germ.  No exact match was found.
