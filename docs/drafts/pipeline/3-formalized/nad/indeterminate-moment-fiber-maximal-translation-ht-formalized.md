# Indeterminate moment fiber maximal-translation HT — formalized

- **ID:** `indeterminate-moment-fiber-maximal-translation-ht-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `indeterminate-moment-fiber-maximal-translation-ht.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Capstone

`HTGeometry.analyticNevCarrierFamily_maximalTranslationPhase_dense_residual` — for every positive
definite normalized moment sequence with bounded kernel at a point, the maximal-translation phase is
dense and residual on every infinite closed boundary face of the representing-measure fiber, with no
analytic hypothesis left.

## The four named constructions

| Item | Declaration |
|---|---|
| Weyl-disc closed form | `NevLeafCauchyMoebius.lean`, `NevLeafInfinityCauchyMoebius.lean` |
| Nevanlinna matrix / analytic carrier family | `analyticNevCarrierFamily`, `exists_classicalAnalyticNevanlinnaCarrierFamily` |
| minimal-exponential-type bound | `analyticNevCarrierFamily_minimalExponentialType`, `nevBinf_hasMinimalExponentialType` |
| N-extremal family | `nevExtremalFamily`, `exists_classicalNevanlinnaExtremalFamily`, `nevExtremalFamily_atoms` |
| analytic parameter-jet family | **`analyticNevCarrierFamilyMaximalTranslationInputs`** (complete term) |

## Supporting layers

`NevanlinnaBauerRetract.lean`, `AnalyticNevanlinnaCarrierBridge.lean`,
`BoundaryCarrierTranslationFreeness.lean`, `NevanlinnaBoundaryFaceMaximalTranslation.lean`,
`CofinalCholeskyResidualPhase.lean`, `StratifiedParametricAvoidance`,
`ProjectiveIncidenceHausdorffDimension`, `CompactConvexExtremeGdelta.lean` (`isGδ_extremePoints`,
`(29)`–`(30)`), `CauchyMomentFlatness.lean` (all-order flatness `(9)`),
`MutuallySingularTotalVariation.lean` (`(20)`–`(22)`), `MomentFunctionalPositivity.lean` and
`MomentFunctionalHaviland.lean` (Hankel positivity, Cauchy–Schwarz, Haviland),
`StieltjesTransformPick.lean` (the Cauchy transform is a Pick function).

## Verification

```text
lake build GaloisForLFunctions.HTGeometry
```

Every declaration resolves and `#print axioms` reports exactly `propext`, `Classical.choice`,
`Quot.sound`.

## Boundary

The card's remaining gate is the external specialist moment-problem and differential-algebra
literature audit.  Two earlier logs on the card ("`MaximalTranslationInputs` is uninhabitable",
"M. Riesz's theorem is a single named hypothesis") were superseded: the field was restated with the
pole in the lower half-plane and is discharged by `analyticNevCarrierFamily_lowerMap`, and the
minimal-type hypothesis is now proved.
