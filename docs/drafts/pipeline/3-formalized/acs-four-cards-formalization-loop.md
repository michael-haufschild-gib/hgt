# ACS four-card formalization loop

- **ID:** acs-four-cards-loop
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every claim of the four ACS cards is formalized; the cards are in 3-formalized.

## Cards
| Card | Lean modules |
|---|---|
| [acs-pvc-cancellation-on-square-multiple-cofactors](acs-pvc-cancellation-on-square-multiple-cofactors.md) | TheClippedSquareComplement, OppositePrimeSignalsOnSquareMultiples |
| [acs-pvc-first-primes-beyond-the-conductor](acs-pvc-first-primes-beyond-the-conductor.md) | OnePrimeCutForEveryConductorInTheFragment, TheContinuousPrimeMassAtTheCofactorEndpoint, RestoringTheLowerProductsForACommonPrimeCut, ConductorSmoothingBeyondTheSplineKnots, TheFirstPrimesThroughTheNineteenTenthsScale, CancellationInTheLongCofactorInterval, SeventhDifferencesAcrossTheSignedCofactors, RHTower/BurnolAlternatingHarmonic |
| [acs-pvc-interior-shell-at-seven-fourths](acs-pvc-interior-shell-at-seven-fourths.md) | InteriorProductShells, TheSevenFourthsConductorShell, TheSeventeenNinthsConductorPrefix |
| [acs-pvc-the-quadratic-product-divider](acs-pvc-the-quadratic-product-divider.md) | TheFirstEndpointAboveTheMovingProductCut, ThePrimeMassAtAQuadraticProductDivider, TheResidueOfTheFirstProductEndpoint, TheFixedPrimeCutAfterSummingConductors, CountingHolography/Sections/TheMellinKernelOfSquareConductorPrices, CountingHolography/Sections/OneSidedBoundsForTheSquareGeneratorPrefix, RHTower/ChebyshevErrorExponentLaw |

All twenty modules compile with `lake --old env lean`; no sorry; printed axioms are propext, Classical.choice, Quot.sound. All are wired into their umbrellas.
