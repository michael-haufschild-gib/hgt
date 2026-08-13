# Canonical Schur truncations cross from rational DA interior to singular maximal-HT boundary only cofinally — formalized

- **ID:** `singular-maximal-ht-schur-defect-collapse-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `singular-maximal-ht-schur-defect-collapse-law.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/BernsteinSzegoProbabilityApproximation.lean` | literal Bernstein–Szegő probability measures, exact finite Toeplitz-Gram reproduction, positive real-analytic densities, and weak convergence to the target circle probability |
| `HTGeometry/CircleCaratheodoryApproximation.lean` | locally uniform convergence of the genuine Carathéodory transforms on every closed subdisk |
| `HTGeometry/BernsteinSzegoCaratheodoryRational.lean` | the zero-free reversed-OPUC denominator and finite numerator: each truncation transform is a rational function, hence satisfies an order-zero differential-algebraic relation on the disk |
| `HTGeometry/SingularSchurDefectCollapse.lean` | strict positivity of every finite determinant-ratio Schur defect, the cofinal collapse of defects, determinant-root, least-eigenvalue and inverse-Cholesky escape, and singular small-aperture concentration with all-`Lᵖ` blow-up |
| `HTGeometry/FAndMRieszVanishing.lean`, `HTGeometry/FAndMRieszConsequences.lean`, `HTGeometry/RieszSingularSzegoCollapse.lean` | the F. and M. Riesz one-sided density theorem and the singular Szegő collapse derived from it |
| `HTGeometry/NevExtremalFamily.lean`, `HTGeometry/AnalyticNevanlinnaCarrierConstruction.lean`, `HTGeometry/NevanlinnaTransferMinimalType.lean`, `HTGeometry/AnalyticNevanlinnaMaximalTranslationInputs.lean` | the constructed `N`-extremal Nevanlinna family and its complete `MaximalTranslationInputs` term |
| `HTGeometry/CofinalCholeskyResidualPhase.lean`, `HTGeometry/AnalyticNevCofinalCholeskyUnconditional.lean` | the residual singular-continuous maximal-translation phase on the real-line carrier simplex, with no structure input |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `GaloisForLFunctions.HTGeometry.singularSchurDefect_doubleBoundary_of_mutuallySingular` — for
  every infinite-support circle probability singular to Lebesgue measure, the Schur-defect collapse
  **and** the Bernstein–Szegő cofinal approximation hold; both boundaries are crossed only in the
  limit;
- `GaloisForLFunctions.HTGeometry.pureSingularCarrier_trichotomy` — the F. and M. Riesz input is
  supplied internally, so graph saturation, analytic completeness, least-eigenvalue collapse,
  determinant escape and frame-norm escape hold with singularity as the only hypothesis;
- `HTGeometry.analyticNevCarrierFamily_cofinalCholeskyResidualPhase_dense_gdelta_residual` and
  `HTGeometry.analyticNevCarrierFamily_cofinalPhase_isSingularContinuous_maximalTranslation` — the
  real-line half: on the canonical Nevanlinna Bauer simplex of every indeterminate normalised
  moment sequence the singular-continuous maximal-translation carriers form a dense `Gδ`, hence
  residual, set.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/AnalyticNevCofinalCholeskyUnconditional.lean
```

Six-declaration axiom audit: `propext`, `Classical.choice`, `Quot.sound` only.

## What closed last

The card's single open formalization gate was "unconditional Nevanlinna-family construction for the
residual real-line phase".  The construction (`nevExtremalFamily`) together with the complete
`MaximalTranslationInputs` term removes the last structure argument from the real-line capstone, so
the card's two halves — circle double boundary and real-line residual phase — are now both
unconditional.

## Boundary

The remaining gates on the paper card are an independent specialist proof audit and a full
primary-source priority audit: external literature obligations, not formalization obligations.  The
Xi double-boundary signature is stated conditionally on the oriented Xi source and is not claimed
here.  This is not a proof of RH.
