## Exceptional layer theory — four proof modules

All four modules pass and are imported by [ExceptionalLayerTheory.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory.lean). Each pipeline card lists the verified declarations.

- [RemovingPrimeLogarithmsPreservesBothIntervalOscillations.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/RemovingPrimeLogarithmsPreservesBothIntervalOscillations.lean) — Passes, including `forward_prime_logarithm_bounds`; `.olean` built. [Pipeline card](../../drafts/pipeline/1-in-progress/local-prime-count-oscillations-on-one-doubling-interval.md)
- [TheMellinEnergyOfTheLastQuotientClasses.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheMellinEnergyOfTheLastQuotientClasses.lean) — Passes: Mellin cell sum, interval integrability, cross-energy and tail identities. The Riesz-basis claim is open and not formalized. [Pipeline card](../../drafts/pipeline/1-in-progress/the-energy-of-the-last-quotient-classes.md)
- [MixingTwoPrimeDilationsRemovesQuartetAliasing.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/MixingTwoPrimeDilationsRemovesQuartetAliasing.lean) — Passes; `.olean` built, as is the dependency [TwoAndThreeDilationRecurrencesAndSingleQuartetStratum.olean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TwoAndThreeDilationRecurrencesAndSingleQuartetStratum.lean). [Pipeline card](../../drafts/pipeline/1-in-progress/mixing-two-prime-dilations-pins-the-quartet.md)
- [SignedFloorComparisonsForOrdinaryPrimes.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SignedFloorComparisonsForOrdinaryPrimes.lean) — Passes; the dependency [RationalGridJumpsOfRealFloorSums.olean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/RationalGridJumpsOfRealFloorSums.lean) is built. The sharper logarithmic asymptotic is conjectural and not formalized. [Pipeline card](../../drafts/pipeline/1-in-progress/signed-floor-comparisons-for-unweighted-prime-counts.md)

## Counting holography — section modules

All fourteen modules pass and are imported by [CountingHolography.lean](../../../formal/GaloisForLFunctions/CountingHolography.lean).

| Lean file | Status |
| --- | --- |
| [FinitePlaceCostOfTheStirlingRemainder.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/FinitePlaceCostOfTheStirlingRemainder.lean) | Passes; `.olean` built. |
| [ThePrimeMassAtTheEndOfADyadicOrbit.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/ThePrimeMassAtTheEndOfADyadicOrbit.lean) | Passes. |
| [TheRealDegreeErrorForTheSquarePrimeWeight.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheRealDegreeErrorForTheSquarePrimeWeight.lean) | Passes. |
| [TheMellinKernelOfSquareConductorPrices.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheMellinKernelOfSquareConductorPrices.lean) | Passes; `.olean` built. |
| [OneSidedBoundsForTheSquareGeneratorPrefix.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/OneSidedBoundsForTheSquareGeneratorPrefix.lean) | Passes. |
| [BoundsFromSuccessiveDoublingDifferences.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/BoundsFromSuccessiveDoublingDifferences.lean) | Passes; `.olean` built. |
| [DoublingOnThreeFixedMultiplicities.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/DoublingOnThreeFixedMultiplicities.lean) | Passes. |
| [OneMultiplicityOnThePoleHyperplane.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/OneMultiplicityOnThePoleHyperplane.lean) | Passes; `.olean` built. |
| [UnitMultiplicityOnThePoleHyperplane.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/UnitMultiplicityOnThePoleHyperplane.lean) | Passes; `.olean` built. |
| [FourSquareGraphsWithBothPoleDegreesZero.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/FourSquareGraphsWithBothPoleDegreesZero.lean) | Passes, including `singleton_pole_dispersion`; `.olean` built. |
| [TheSecondDoublingDifferenceOfFourSquareGraphs.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheSecondDoublingDifferenceOfFourSquareGraphs.lean) | Passes. |
| [FiveUnitGraphsOnTheTwoPoleHyperplane.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/FiveUnitGraphsOnTheTwoPoleHyperplane.lean) | Passes. |
| [ThePositiveInverseOfTheTwoPoleFilter.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/ThePositiveInverseOfTheTwoPoleFilter.lean) | Passes; `.olean` built. |
| [SmallSectionsOnTwoPoleFreeTranslates.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/SmallSectionsOnTwoPoleFreeTranslates.lean) | Passes. |

Proof cards with Lean status: [Factorial majorants](../../drafts/pipeline/1-in-progress/factorial-majorants-for-the-square-prime-profile.md) · [Dyadic prime mass](../../drafts/pipeline/1-in-progress/the-prime-mass-escaping-along-dyadic-square-conductors.md) · [Signed square prefixes](../../drafts/pipeline/1-in-progress/the-product-of-square-generators-over-all-smaller-conductors.md) · [Four pole-cancelling graphs](../../drafts/pipeline/1-in-progress/four-square-graphs-cancelling-both-poles.md) · [Unit-multiplicity triples](../../drafts/pipeline/1-in-progress/pole-balanced-triples-of-unit-multiplicity.md) · [Two-pole filter](../../drafts/pipeline/1-in-progress/the-positive-inverse-of-the-two-pole-filter.md).

## Paper-proof formalizations — 12 modules

All twelve modules pass and are imported by their umbrellas. The prerequisite oleans [LabelledArrangementRecovery](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/Codes/LabelledArrangementRecovery.lean) and [FiniteFieldPoints](../../../formal/GaloisForLFunctions/HTGeometry/StanleyReisner/FiniteFieldPoints.lean) are built.

| Lean file | Status | Umbrella |
| --- | --- | --- |
| [PolynomialCountGlobalProduct.lean](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/Zeta/PolynomialCountGlobalProduct.lean) | Passes, including `countGlobalZeta_order`. | [ArithmeticCastelnuovoSeveri.lean](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri.lean) |
| [PolynomialCountWittEmbedding.lean](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/Zeta/PolynomialCountWittEmbedding.lean) | Passes. | [ArithmeticCastelnuovoSeveri.lean](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri.lean) |
| [SparseExtensionRecovery.lean](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/Zeta/SparseExtensionRecovery.lean) | Passes. | [ArithmeticCastelnuovoSeveri.lean](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri.lean) |
| [OptimalArrangementAlphabets.lean](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/Codes/OptimalArrangementAlphabets.lean) | Passes. | [ArithmeticHarmonicAnalysis.lean](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis.lean) |
| [StellarPointCounts.lean](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/Codes/StellarPointCounts.lean) | Passes. | [ArithmeticHarmonicAnalysis.lean](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis.lean) |
| [ReflectionlessModeCollocation.lean](../../../formal/GaloisForLFunctions/HTGeometry/Analysis/ReflectionlessModeCollocation.lean) | Passes. | [HTGeometry.lean](../../../formal/GaloisForLFunctions/HTGeometry.lean) |
| [FaceRingHilbertKunz.lean](../../../formal/GaloisForLFunctions/HTGeometry/StanleyReisner/FaceRingHilbertKunz.lean) | Passes. | [HTGeometry.lean](../../../formal/GaloisForLFunctions/HTGeometry.lean) |
| [NodalKoszulNormalForm.lean](../../../formal/GaloisForLFunctions/HTGeometry/StanleyReisner/NodalKoszulNormalForm.lean) | Passes. | [HTGeometry.lean](../../../formal/GaloisForLFunctions/HTGeometry.lean) |
| [NodalResidueFibers.lean](../../../formal/GaloisForLFunctions/HTGeometry/StanleyReisner/NodalResidueFibers.lean) | Passes. | [HTGeometry.lean](../../../formal/GaloisForLFunctions/HTGeometry.lean) |
| [SparsePowerSeriesMinors.lean](../../../formal/GaloisForLFunctions/HilbertMetric/Kernels/SparsePowerSeriesMinors.lean) | Passes. | [HilbertMetric.lean](../../../formal/GaloisForLFunctions/HilbertMetric.lean) |
| [CanonicalBinaryMinorBounds.lean](../../../formal/GaloisForLFunctions/RepresentationLifting/Lattices/CanonicalBinaryMinorBounds.lean) | Passes. | [RepresentationLifting.lean](../../../formal/GaloisForLFunctions/RepresentationLifting.lean) |
| [UniformIncidenceCokernels.lean](../../../formal/GaloisForLFunctions/RepresentationLifting/Lattices/UniformIncidenceCokernels.lean) | Passes. | [RepresentationLifting.lean](../../../formal/GaloisForLFunctions/RepresentationLifting.lean) |

## Eight-paper applications

All thirteen modules pass and are imported by their umbrellas.

| Lean file | Status | Umbrella |
| --- | --- | --- |
| [ResonancesAndCurvatureOfExponentialSums.lean](../../../formal/GaloisForLFunctions/PrimeExponentialSums/ResonancesAndCurvatureOfExponentialSums.lean) | Passes, including `pair_dispersion`. | [PrimeExponentialSums.lean](../../../formal/GaloisForLFunctions/PrimeExponentialSums.lean) |
| [ValuesInARestrictionFiber.lean](../../../formal/GaloisForLFunctions/HeckeLFunctions/Characters/ValuesInARestrictionFiber.lean) | Passes. | [HeckeLFunctions.lean](../../../formal/GaloisForLFunctions/HeckeLFunctions.lean) |
| [FirstDetectionOfAnInvolution.lean](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/FiniteGroup/FirstDetectionOfAnInvolution.lean) | Passes, including `parity_balance` and `exact_layer`. | [ArithmeticHarmonicAnalysis.lean](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis.lean) |
| [MeanCostOfTheHigherDyadicRanks.lean](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/FiniteGroup/MeanCostOfTheHigherDyadicRanks.lean) | Passes. | [ArithmeticHarmonicAnalysis.lean](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis.lean) |
| [PrincipalRamanujanTransferOnTheDisk.lean](../../../formal/GaloisForLFunctions/PrimeExponentialSums/PrincipalRamanujanTransferOnTheDisk.lean) | Passes, including `hasSum_transfer`; `.olean` built. | [PrimeExponentialSums.lean](../../../formal/GaloisForLFunctions/PrimeExponentialSums.lean) |
| [ExactDiskImageOfThePrincipalTransfer.lean](../../../formal/GaloisForLFunctions/PrimeExponentialSums/ExactDiskImageOfThePrincipalTransfer.lean) | Passes. | [PrimeExponentialSums.lean](../../../formal/GaloisForLFunctions/PrimeExponentialSums.lean) |
| [ConductorShellOfTheLocalGaussTransfer.lean](../../../formal/GaloisForLFunctions/PrimeExponentialSums/ConductorShellOfTheLocalGaussTransfer.lean) | Passes; `.olean` built. | [PrimeExponentialSums.lean](../../../formal/GaloisForLFunctions/PrimeExponentialSums.lean) |
| [SharpGapBelowPrimitiveGaussTransfers.lean](../../../formal/GaloisForLFunctions/PrimeExponentialSums/SharpGapBelowPrimitiveGaussTransfers.lean) | Passes. | [PrimeExponentialSums.lean](../../../formal/GaloisForLFunctions/PrimeExponentialSums.lean) |
| [AllDeterminantsOfACongruenceLattice.lean](../../../formal/GaloisForLFunctions/CollectiveDiophantineGeometry/AllDeterminantsOfACongruenceLattice.lean) | Passes; `.olean` built. | [CollectiveDiophantineGeometry.lean](../../../formal/GaloisForLFunctions/CollectiveDiophantineGeometry.lean) |
| [UnitFractionWitnessGram.lean](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/Divisors/UnitFractionWitnessGram.lean) | Passes. | [BezoutValuationIncidence.lean](../../../formal/GaloisForLFunctions/BezoutValuationIncidence.lean) |
| [SignsAndPrincipalUnitsAtTwo.lean](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/FiniteGroup/SignsAndPrincipalUnitsAtTwo.lean) | Passes. | [ArithmeticHarmonicAnalysis.lean](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis.lean) |
| [VerticalFrequenciesOfAnIntegerLattice.lean](../../../formal/GaloisForLFunctions/CollectiveDiophantineGeometry/VerticalFrequenciesOfAnIntegerLattice.lean) | Passes. | [CollectiveDiophantineGeometry.lean](../../../formal/GaloisForLFunctions/CollectiveDiophantineGeometry.lean) |
| [EdgePhasesOfAnIntegerCharge.lean](../../../formal/GaloisForLFunctions/HTGeometry/Quantum/EdgePhasesOfAnIntegerCharge.lean) | Passes. | [HTGeometry.lean](../../../formal/GaloisForLFunctions/HTGeometry.lean) |

## Shared midpoint encoding on prime displacement planes (§2.5)

Both modules pass and are imported by [CountingHolography.lean](../../../formal/GaloisForLFunctions/CountingHolography.lean) after `ReversibleCarryOnMixedSectionFamilies`. The [pipeline card](../../drafts/pipeline/3-formalized/adelic-midpoint-carry-on-prime-displacement-planes.md) is in `3-formalized`.

| Lean file | Status |
| --- | --- |
| [AdelicCarryOnSectionRepresentatives.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/AdelicCarryOnSectionRepresentatives.lean) | Passes; `.olean` built. |
| [SharedMidpointEncodingOnPrimeDisplacementPlanes.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/SharedMidpointEncodingOnPrimeDisplacementPlanes.lean) | Passes. Its headline theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. |

## Two-interval quartet amplitude and ordinary-prime obstruction (§2.17)

All five modules pass and are imported by [ZeroConfigurationGeometry.lean](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry.lean) or [ExceptionalLayerTheory.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory.lean). The [pipeline card](../../drafts/pipeline/3-formalized/review-1811-2-17-two-interval-quartet-amplitude.md) is in `3-formalized`.

| Lean file | Status | Umbrella |
| --- | --- | --- |
| [TwoIntervalAmplitudeAliasingAndCoprimeRealization.lean](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/TwoIntervalAmplitudeAliasingAndCoprimeRealization.lean) | Passes; `.olean` built. | [ZeroConfigurationGeometry.lean](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry.lean) |
| [RemovingPrimeLogarithmsPreservesBothIntervalOscillations.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/RemovingPrimeLogarithmsPreservesBothIntervalOscillations.lean) | Passes; `.olean` built. | [ExceptionalLayerTheory.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory.lean) |
| [TwoAndThreeDilationRecurrencesAndSingleQuartetStratum.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TwoAndThreeDilationRecurrencesAndSingleQuartetStratum.lean) | Passes; `.olean` built. | [ExceptionalLayerTheory.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory.lean) |
| [MixingTwoPrimeDilationsRemovesQuartetAliasing.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/MixingTwoPrimeDilationsRemovesQuartetAliasing.lean) | Passes; `.olean` built. | [ExceptionalLayerTheory.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory.lean) |
| [TwoIntervalQuartetAmplitudeAndOrdinaryPrimeObstruction.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TwoIntervalQuartetAmplitudeAndOrdinaryPrimeObstruction.lean) | Passes; `.olean` built. Depends only on `propext`, `Classical.choice` and `Quot.sound`. | [ExceptionalLayerTheory.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory.lean) |
