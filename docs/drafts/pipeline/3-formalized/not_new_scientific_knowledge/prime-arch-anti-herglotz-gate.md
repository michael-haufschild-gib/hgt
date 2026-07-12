# Prime--archimedean anti-Herglotz gate to RH

- **ID:** `prime-arch-anti-herglotz-gate`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / RH-SUFFICIENT CRITERION
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeArchAntiHerglotzGate.lean`
- **Statement:** Left-half accretivity of the completed continued prime--Gamma flux forces the
  Riemann Hypothesis through a scalar anti-Herglotz pole-exclusion argument.

## Formal theorem chain

Lean proves

```text
CompletedPrimeGammaLeftHalfAccretive
  -> ContinuedPrimeArchUpperAntiHerglotz
  -> RiemannHypothesis.
```

The public declarations are:

```text
continuedPrimeArchUpperAntiHerglotz_of_completedPrimeGammaLeftHalfAccretive
riemannHypothesis_of_continuedPrimeArchUpperAntiHerglotz
riemannHypothesis_of_completedPrimeGammaLeftHalfAccretive
```

The proof uses the existing source identity only after the hypothesized source sign is fixed. A
hypothetical off-line zero is reflected into the left half-strip; the positive multiplicity of its
local logarithmic-derivative residue then produces a nearby source value with the forbidden sign.

## Status boundary

This card records the formalized implication, not a proof of its premise. The independent
prime--Gamma or theta positivity theorem needed to discharge
`CompletedPrimeGammaLeftHalfAccretive` remains in
`../../1-in-progress/completed-prime-gamma-left-half-accretivity-to-rh.md`.

## Countable strengthening

The same Lean module additionally defines `gaussianRatPoint`, proves its range dense in `Complex`,
and proves

```text
completedPrimeGammaLeftHalfAccretive_of_gaussianRat
riemannHypothesis_of_completedPrimeGammaGaussianRatLeftHalfAccretive.
```

Consequently the RH-sufficient source sign is a countable value family indexed by `Rat x Rat`.
