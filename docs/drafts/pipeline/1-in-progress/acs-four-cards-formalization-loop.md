# ACS four-card formalization loop

- **ID:** acs-four-cards-loop
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Statement:** Formalize every claim of the four cards in docs/drafts/pipeline/2-fully-proven/acs and move them to 3-formalized.

## Cards and Lean coverage
| Card | Status |
|---|---|
| acs-pvc-cancellation-on-square-multiple-cofactors | all claims in Lean (TheClippedSquareComplement, OppositePrimeSignalsOnSquareMultiples); final audit pending |
| acs-pvc-first-primes-beyond-the-conductor | gaps closed: cap_free_prime_power_fragments now for 12/7 ≤ a < 2, cofactorDensityRamp_interval_lengths / _cell; audit clean |
| acs-pvc-interior-shell-at-seven-fourths | all claims in Lean (InteriorProductShells horizonPair_bound = per-pair third difference; TheSevenFourthsConductorShell; TheSeventeenNinthsConductorPrefix); final audit pending |
| acs-pvc-the-quadratic-product-divider | gaps closed: seventeenNinths_fixed_cut_leading_terms, squareDivider_real_poles_cancel, firstEndpointPrice_discrepancy, firstEndpoint_discrepancy_analytic; audit of older modules pending |

## Final audit list (one foreground compile each)
Clean (standard axioms): TheContinuousPrimeMassAtTheCofactorEndpoint, TheFirstPrimesThroughTheNineteenTenthsScale,
TheFixedPrimeCutAfterSummingConductors (olean rebuilt), TheResidueOfTheFirstProductEndpoint, TheClippedSquareComplement,
OppositePrimeSignalsOnSquareMultiples, OnePrimeCutForEveryConductorInTheFragment, BurnolAlternatingHarmonic,
RestoringTheLowerProductsForACommonPrimeCut, ConductorSmoothingBeyondTheSplineKnots, CancellationInTheLongCofactorInterval,
SeventhDifferencesAcrossTheSignedCofactors.
Pending: InteriorProductShells, TheSevenFourthsConductorShell, TheSeventeenNinthsConductorPrefix,
TheMellinKernelOfSquareConductorPrices, ChebyshevErrorExponentLaw, OneSidedBoundsForTheSquareGeneratorPrefix,
TheFirstEndpointAboveTheMovingProductCut, ThePrimeMassAtAQuadraticProductDivider.

## Log
- 2026-11-20 — loop resumed; coverage mapped.
