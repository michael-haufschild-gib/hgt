# Xi folder stage-3 formalization ledger

Target: every card in `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/xi/`
formalized unconditionally in Lean and promoted to `3-formalized`.

## Status

| # | Card | State | Lean modules |
|---|---|---|---|
| 1 | xi-determinant-logarithmic-singular-value-law | open | |
| 2 | xi-gamma-shape-completely-monotone-rh | open | |
| 3 | xi-global-meixner-shape-landau-rh | open | |
| 4 | xi-hedenmalm-local-algebra-rank-census | Lean done | HTGeometry/PolynomialQuotientMultiplicationRank, HTGeometry/GcdDerivativeDistinctRoots, HTGeometry/HermiteBiehlerPairRankCensus, HTGeometry/FiniteMomentDivisorReconstruction, RHTower/XiHedenmalmLocalAlgebraRankCensus |
| 5 | xi-orientation-euler-safe-paired-cauchy-completeness | open | |
| 6 | xi-outer-euler-modulus-first-prime-seam-antialignment | open | |
| 7 | xi-positive-paired-real-loewner-seam-log-weld | open | |
| 8 | xi-prime-seam-one-ended-cofinal-edge-collapse | Lean done (tensor essential-norm gate belongs to parent card) | HTGeometry/ArbitraryLabelEndReconstruction, RHTower/XiPrimeSeamOneEndedCollapse |
| 9 | xi-radial-jensen-schur-capacity-rigidity | open | |
| 10 | xi-reciprocal-translation-prime-seam-norm-law | open | |
| 11 | xi-shift-loewner-prime-generator-law | open | |
| 12 | xi-square-descent-vertical-modulus-rh | open | |
| 13 | xi-supercharge-persistent-harnack-defect | open | |
| 14 | xi-unit-euler-pole-affine-section-translated-bezoutian | open | |
| 15 | xi-theta-square-rate-hardy-reader | open | |

## Reusable corpus assets found

- `HTGeometry/CoherenceEndReconstruction.lean` — finite-boundary one-ended reconstruction.
- `RHTower/XiPrimeSeamCoherenceCollapse.lean` — canonical prime seam, cofinal decay.
- `RHTower/HeatAperturePrimeSeamReflection.lean` — single prime seam pins the critical line.
- `HTGeometry/QuotientIdealDimension.lean` — finite local algebra dimension and ideal codimension.
- `HTGeometry/PowerSumTorelli.lean`, `MultisetNewtonSolve.lean` — Newton inversion.
- `RHTower/SlabGermResidueTransport.lean` — contour power moments = multiplicity divisor moments.
- `RHTower/XiGuinandWeilRectanglePeeling.lean` — weighted rectangle argument principle for `XiC`.
- `RHTower/SchattenCriticalAsymptotic.lean`, `SoninEulerFiniteL2Lower.lean` — Schatten/Calkin layer.
