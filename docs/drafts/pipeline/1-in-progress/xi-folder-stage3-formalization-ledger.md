# Xi folder stage-3 formalization ledger

Target: every card in `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/xi/`
formalized unconditionally in Lean and promoted to `3-formalized`.

## Status

| # | Card | State | Lean modules |
|---|---|---|---|
| 1 | xi-determinant-logarithmic-singular-value-law | open | |
| 2 | xi-gamma-shape-completely-monotone-rh | partial: complete monotonicity, Hankel positivity, exp counterexample done; CM-extension⇒RH still needs the Hausdorff/Bernstein consumer | RHTower/XiGammaShapeCompleteMonotonicity |
| 3 | xi-global-meixner-shape-landau-rh | Lean done | HTGeometry/GeneralDirichletLandau, RHTower/XiGlobalMeixnerShapeLandau |
| 4 | xi-hedenmalm-local-algebra-rank-census | Lean done | HTGeometry/PolynomialQuotientMultiplicationRank, HTGeometry/GcdDerivativeDistinctRoots, HTGeometry/HermiteBiehlerPairRankCensus, HTGeometry/FiniteMomentDivisorReconstruction, RHTower/XiHedenmalmLocalAlgebraRankCensus |
| 5 | xi-orientation-euler-safe-paired-cauchy-completeness | open | |
| 6 | xi-outer-euler-modulus-first-prime-seam-antialignment | Lean done | RHTower/XiOuterEulerModulusPrimeSeamAntialignment |
| 7 | xi-positive-paired-real-loewner-seam-log-weld | Lean done (targets 1-5) | RHTower/XiPositivePairedRealLoewnerSeam |
| 8 | xi-prime-seam-one-ended-cofinal-edge-collapse | Lean done (tensor essential-norm gate belongs to parent card) | HTGeometry/ArbitraryLabelEndReconstruction, RHTower/XiPrimeSeamOneEndedCollapse |
| 9 | xi-radial-jensen-schur-capacity-rigidity | Lean done | HTGeometry/SchwarzPickEstimate, RHTower/XiRadialJensenSchurCapacity |
| 10 | xi-reciprocal-translation-prime-seam-norm-law | Lean done | RHTower/XiReciprocalTranslationSeamNormLaw |
| 11 | xi-shift-loewner-prime-generator-law | open | |
| 12 | xi-square-descent-vertical-modulus-rh | Lean done (both directions + R* corollary) | RHTower/XiSquareDescentVerticalModulus, RHTower/XiSquareDescentVerticalModulusConverse |
| 13 | xi-supercharge-persistent-harnack-defect | open | |
| 14 | xi-unit-euler-pole-affine-section-translated-bezoutian | open | |
| 15 | xi-theta-square-rate-hardy-reader | open | |

## Remaining infrastructure to build

| Card | Missing classical input |
|---|---|
| 1 | Riemann–von Mangoldt asymptotic in operator form; compact-operator singular values, Schatten ideals, `det_2` |
| 2 | Bernstein/Hausdorff consumer: CM function on `(0,∞)` ⇒ Hausdorff source ⇒ summability at every positive shape |
| 5 | meromorphic Cauchy-transform completeness on the Xi `ell^2` carrier |
| 11 | Nevanlinna–Pick extension for Caratheodory functions on a half plane |
| 13 | real hyperelliptic topology: genus, real components, Harnack bound |
| 14 | Hadamard factorization for even entire functions of order `< 1` (genus zero) |
| 15 | right half-plane Hardy space `H^2` and the Laplace Paley–Wiener unitary |

## Reusable corpus assets found

- `HTGeometry/CoherenceEndReconstruction.lean` — finite-boundary one-ended reconstruction.
- `RHTower/XiPrimeSeamCoherenceCollapse.lean` — canonical prime seam, cofinal decay.
- `RHTower/HeatAperturePrimeSeamReflection.lean` — single prime seam pins the critical line.
- `HTGeometry/QuotientIdealDimension.lean` — finite local algebra dimension and ideal codimension.
- `HTGeometry/PowerSumTorelli.lean`, `MultisetNewtonSolve.lean` — Newton inversion.
- `RHTower/SlabGermResidueTransport.lean` — contour power moments = multiplicity divisor moments.
- `RHTower/XiGuinandWeilRectanglePeeling.lean` — weighted rectangle argument principle for `XiC`.
- `RHTower/SchattenCriticalAsymptotic.lean`, `SoninEulerFiniteL2Lower.lean` — Schatten/Calkin layer.
- `HTGeometry/HausdorffMomentTheorem.lean` — Hausdorff moment theorem with uniqueness.
- `HTGeometry/GeneralDirichletLandau.lean` (NEW) — Landau for general Dirichlet series, Taylor
  expansion at a safe centre, complete monotonicity, radial Hankel positivity.
- `HTGeometry/SchwarzPickEstimate.lean` (NEW) — sharp Schwarz–Pick displacement, narrow-sector
  Schur lemma.
