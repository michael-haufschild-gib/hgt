# Singular maximal-HT carriers saturate the canonical Toeplitz weld graph — formalized

- **ID:** `singular-maximal-ht-toeplitz-weld-graph-saturation-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `singular-maximal-ht-toeplitz-weld-graph-saturation.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/GraphSaturationCore.lean`, `HTGeometry/ToeplitzPolynomialGraph.lean` | the polynomial weld graph as a submodule, its exact orthogonal complement, and the reduction of closure to triviality of the monomial annihilator |
| `HTGeometry/RieszBrothersReduction.lean`, `HTGeometry/FAndMRieszVanishing.lean`, `HTGeometry/FAndMRieszConsequences.lean` | the reduction to one-sided Fourier rigidity and the F. and M. Riesz theorem that discharges it |
| `HTGeometry/PureSingularCarrierTrichotomy.lean` | raw graph saturation, analytic-polynomial completeness, least-eigenvalue collapse, determinant escape, inverse-Cholesky operator-norm escape |
| `HTGeometry/PureSingularCarrierUnitary.lean`, `HTGeometry/FAndMRieszUnitaryConsequences.lean` | the coherent onto unitary carrier frame built from the canonical inverse-Cholesky tower |
| `HTGeometry/BernsteinSzegoReconstruction.lean` | exact finite Toeplitz-section reconstruction by the canonical Bernstein–Szegő carrier |
| `HTGeometry/BernsteinSzegoWeldBounds.lean` | uniform positive lower and finite upper bounds for every finite Bernstein–Szegő polynomial weld |
| `HTGeometry/CholeskyDeterminantDivergence.lean` | the exact repair-norm identity `‖C_N‖₂ = λ_min(G_N)^(-1/2)` and its divergence |
| `HTGeometry/NevExtremalFamily.lean`, `HTGeometry/AnalyticNevanlinnaCarrierConstruction.lean`, `HTGeometry/AnalyticNevanlinnaMaximalTranslationInputs.lean`, `HTGeometry/CofinalCholeskyResidualPhase.lean`, `HTGeometry/AnalyticNevCofinalCholeskyUnconditional.lean` | the constructed Nevanlinna family and the residual real-line phase with no structure input |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `GaloisForLFunctions.HTGeometry.pureSingularCarrier_trichotomy` — **the card's circle capstone,
  unconditional**: for a purely singular infinite-support circle measure the raw weld graph is
  dense in the full product (its closure is the maximally multivalued relation), the analytic
  monomials are complete, and the canonical frame tower escapes in determinant, least eigenvalue
  and operator norm;
- `GaloisForLFunctions.HTGeometry.exists_circleCanonicalCarrierUnitary` — the unique compatible
  positive-triangular repair produces an onto unitary carrier frame;
- `GaloisForLFunctions.HTGeometry.circleToeplitzGram_bernsteinSzegoMoment_eq` — every canonical
  Bernstein–Szegő truncation reproduces the target Gram section through its truncation degree;
- `GaloisForLFunctions.HTGeometry.bernsteinSzego_polynomial_weld_quadratic_bounds` — each finite
  weld is bounded and bounded below;
- `HTGeometry.analyticNevCarrierFamily_cofinalCholeskyResidualPhase_dense_gdelta_residual`,
  `HTGeometry.analyticNevCarrierFamily_cofinalPhase_isSingularContinuous_maximalTranslation` — the
  saturated-raw / divergent-unitary phase occurs on a residual set of singular-continuous
  maximal-translation carriers of every indeterminate normalised moment fiber.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/AnalyticNevCofinalCholeskyUnconditional.lean
```

## What closed last

The card's single open formalization gate was "unconditional Nevanlinna-family construction for the
residual real-line phase"; it is discharged by `nevExtremalFamily` together with
`analyticNevCarrierFamilyMaximalTranslationInputs`, so the residual-phase capstone takes no
structure argument.

## Boundary

The remaining gates are an independent specialist proof audit and a full primary-source priority
audit — external literature obligations.  The RH consequence is stated as a carrier requirement
only; no orientation claim is made.
