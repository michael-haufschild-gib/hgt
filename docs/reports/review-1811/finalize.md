## Exceptional layer theory — four pending proof modules

After each module passes, add its import to [ExceptionalLayerTheory.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory.lean) and link the verified declarations on its pipeline card.

- [RemovingPrimeLogarithmsPreservesBothIntervalOscillations.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/RemovingPrimeLogarithmsPreservesBothIntervalOscillations.lean) — Check the revised proof of `forward_prime_logarithm_bounds`. The last check was interrupted before an exit result. [Pipeline card](../../drafts/pipeline/1-in-progress/local-prime-count-oscillations-on-one-doubling-interval.md)
- [TheMellinEnergyOfTheLastQuotientClasses.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheMellinEnergyOfTheLastQuotientClasses.lean) — Check repairs to the Mellin cell sum, interval integrability, and cross-energy and tail identities. The Riesz-basis claim remains open. [Pipeline card](../../drafts/pipeline/1-in-progress/the-energy-of-the-last-quotient-classes.md)
- [MixingTwoPrimeDilationsRemovesQuartetAliasing.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/MixingTwoPrimeDilationsRemovesQuartetAliasing.lean) — First check pending. Build the missing [TwoAndThreeDilationRecurrencesAndSingleQuartetStratum.olean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TwoAndThreeDilationRecurrencesAndSingleQuartetStratum.lean) dependency first. [Pipeline card](../../drafts/pipeline/1-in-progress/mixing-two-prime-dilations-pins-the-quartet.md)
- [SignedFloorComparisonsForOrdinaryPrimes.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SignedFloorComparisonsForOrdinaryPrimes.lean) — First check pending. Build the missing [RationalGridJumpsOfRealFloorSums.olean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/RationalGridJumpsOfRealFloorSums.lean) dependency first. The sharper logarithmic asymptotic remains conjectural. [Pipeline card](../../drafts/pipeline/1-in-progress/signed-floor-comparisons-for-unweighted-prime-counts.md)

## Counting holography — outstanding Lean files

Wiring target is [CountingHolography.lean](../../../formal/GaloisForLFunctions/CountingHolography.lean).

| Lean file | Remaining work |
| --- | --- |
| [FinitePlaceCostOfTheStirlingRemainder.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/FinitePlaceCostOfTheStirlingRemainder.lean) | Build the missing dependency olean for ThePrimeMassAtTheEndOfADyadicOrbit. Source previously passed and is already wired. |
| [ThePrimeMassAtTheEndOfADyadicOrbit.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/ThePrimeMassAtTheEndOfADyadicOrbit.lean) | Check the dyadic endpoint, fourth-power boundary and summation-order proofs after the finite-place dependency builds. Fix errors and wire. |
| [TheRealDegreeErrorForTheSquarePrimeWeight.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheRealDegreeErrorForTheSquarePrimeWeight.lean) | Recheck the repaired compact-support, differentiability, Mellin moment and balanced-floor integral proofs. Wire after passing. |
| [TheMellinKernelOfSquareConductorPrices.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheMellinKernelOfSquareConductorPrices.lean) | Recheck the repaired mesh estimates, Dirichlet continuation and prefix integrals. Fix remaining errors, build its olean for OneSidedBoundsForTheSquareGeneratorPrefix and wire. |
| [OneSidedBoundsForTheSquareGeneratorPrefix.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/OneSidedBoundsForTheSquareGeneratorPrefix.lean) | Check the one-sided prefix proof after the Mellin kernel builds. The signed-product dependency already has an olean. Wire after passing. |
| [BoundsFromSuccessiveDoublingDifferences.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/BoundsFromSuccessiveDoublingDifferences.lean) | Check the extracted doubling lemmas and build the missing olean for both doubling modules below. Wire. |
| [DoublingOnThreeFixedMultiplicities.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/DoublingOnThreeFixedMultiplicities.lean) | Check the refactored source against BoundsFromSuccessiveDoublingDifferences. Add its direct umbrella import. |
| [OneMultiplicityOnThePoleHyperplane.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/OneMultiplicityOnThePoleHyperplane.lean) | Check the single-multiplicity comparison, build its missing olean for TheSecondDoublingDifferenceOfFourSquareGraphs and wire. |
| [UnitMultiplicityOnThePoleHyperplane.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/UnitMultiplicityOnThePoleHyperplane.lean) | Check the source edits made after the existing olean. Already wired. |
| [FourSquareGraphsWithBothPoleDegreesZero.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/FourSquareGraphsWithBothPoleDegreesZero.lean) | Earlier check passed. The proof of singleton_pole_dispersion has a subsequent tactic edit. Check current source. Already wired. |
| [TheSecondDoublingDifferenceOfFourSquareGraphs.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheSecondDoublingDifferenceOfFourSquareGraphs.lean) | Check the four-graph width criterion after both missing dependency oleans above exist. Wire after passing. |
| [FiveUnitGraphsOnTheTwoPoleHyperplane.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/FiveUnitGraphsOnTheTwoPoleHyperplane.lean) | Check the five-graph multiplier and degree bounds, including the revised normalization. Wire after passing. |
| [ThePositiveInverseOfTheTwoPoleFilter.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/ThePositiveInverseOfTheTwoPoleFilter.lean) | Check the positive inverse and prime-orbit criterion. Build its missing olean for SmallSectionsOnTwoPoleFreeTranslates and wire. |
| [SmallSectionsOnTwoPoleFreeTranslates.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/SmallSectionsOnTwoPoleFreeTranslates.lean) | Check the translated pairings and prime-orbit power criterion after ThePositiveInverseOfTheTwoPoleFilter builds. Wire after passing. |

Update the corresponding proof cards when their declarations pass. [Factorial majorants](../../drafts/pipeline/1-in-progress/factorial-majorants-for-the-square-prime-profile.md) · [Dyadic prime mass](../../drafts/pipeline/1-in-progress/the-prime-mass-escaping-along-dyadic-square-conductors.md) · [Signed square prefixes](../../drafts/pipeline/1-in-progress/the-product-of-square-generators-over-all-smaller-conductors.md) · [Four pole-cancelling graphs](../../drafts/pipeline/1-in-progress/four-square-graphs-cancelling-both-poles.md) · [Unit-multiplicity triples](../../drafts/pipeline/1-in-progress/pole-balanced-triples-of-unit-multiplicity.md) · [Two-pole filter](../../drafts/pipeline/1-in-progress/the-positive-inverse-of-the-two-pole-filter.md).

## Paper-proof formalizations — 12 modules pending

Check each module, fix any errors, then add its import to the linked umbrella. Both prerequisite sources below already passed and are wired. Their importers need the missing `.olean` files.

| Lean file | Remaining proof work | Umbrella to update |
| --- | --- | --- |
| [PolynomialCountGlobalProduct.lean](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/Zeta/PolynomialCountGlobalProduct.lean) | Check the revised natural-number index in `countGlobalZeta_order`. | [ArithmeticCastelnuovoSeveri.lean](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri.lean) |
| [PolynomialCountWittEmbedding.lean](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/Zeta/PolynomialCountWittEmbedding.lean) | Check the Witt ghost coordinates, integral embedding, and local zeta series identity. | [ArithmeticCastelnuovoSeveri.lean](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri.lean) |
| [SparseExtensionRecovery.lean](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/Zeta/SparseExtensionRecovery.lean) | Check sparse recovery, the sharp collision examples, and the revised polynomial evaluation over finite products. | [ArithmeticCastelnuovoSeveri.lean](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri.lean) |
| [OptimalArrangementAlphabets.lean](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/Codes/OptimalArrangementAlphabets.lean) | Build the [LabelledArrangementRecovery.lean](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/Codes/LabelledArrangementRecovery.lean) olean first. Check the classification of optimal alphabet sizes. | [ArithmeticHarmonicAnalysis.lean](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis.lean) |
| [StellarPointCounts.lean](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/Codes/StellarPointCounts.lean) | The interrupted check returned no exit result. Check the stellar subdivision formula and its point-count specializations. | [ArithmeticHarmonicAnalysis.lean](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis.lean) |
| [ReflectionlessModeCollocation.lean](../../../formal/GaloisForLFunctions/HTGeometry/Analysis/ReflectionlessModeCollocation.lean) | Check strict positivity of the collocation minors and the endpoint eigenmode formula. | [HTGeometry.lean](../../../formal/GaloisForLFunctions/HTGeometry.lean) |
| [FaceRingHilbertKunz.lean](../../../formal/GaloisForLFunctions/HTGeometry/StanleyReisner/FaceRingHilbertKunz.lean) | Build the [FiniteFieldPoints.lean](../../../formal/GaloisForLFunctions/HTGeometry/StanleyReisner/FiniteFieldPoints.lean) olean first. Check the quotient basis and Hilbert–Kunz multiplicity. | [HTGeometry.lean](../../../formal/GaloisForLFunctions/HTGeometry.lean) |
| [NodalKoszulNormalForm.lean](../../../formal/GaloisForLFunctions/HTGeometry/StanleyReisner/NodalKoszulNormalForm.lean) | Check the axis-gluing equivalence, cycle normal form, and both homology groups. | [HTGeometry.lean](../../../formal/GaloisForLFunctions/HTGeometry.lean) |
| [NodalResidueFibers.lean](../../../formal/GaloisForLFunctions/HTGeometry/StanleyReisner/NodalResidueFibers.lean) | Check the divisor-sum fiber count and the prime-power generating series. | [HTGeometry.lean](../../../formal/GaloisForLFunctions/HTGeometry.lean) |
| [SparsePowerSeriesMinors.lean](../../../formal/GaloisForLFunctions/HilbertMetric/Kernels/SparsePowerSeriesMinors.lean) | Check the ordered Cauchy–Binet expansion and strict positivity for the sparse series, cosh, and sinh kernels. | [HilbertMetric.lean](../../../formal/GaloisForLFunctions/HilbertMetric.lean) |
| [CanonicalBinaryMinorBounds.lean](../../../formal/GaloisForLFunctions/RepresentationLifting/Lattices/CanonicalBinaryMinorBounds.lean) | Check the determinant bounds in ranks three through five and the sharp examples modulo three and five. | [RepresentationLifting.lean](../../../formal/GaloisForLFunctions/RepresentationLifting.lean) |
| [UniformIncidenceCokernels.lean](../../../formal/GaloisForLFunctions/RepresentationLifting/Lattices/UniformIncidenceCokernels.lean) | Check the incidence cokernel and the joint rank–corank gcd criterion. | [RepresentationLifting.lean](../../../formal/GaloisForLFunctions/RepresentationLifting.lean) |

## Eight-paper applications — remaining Lean files

Eight modules need a successful Lean check and an umbrella import.

| Lean file | Remaining work | Umbrella to update |
| --- | --- | --- |
| [ResonancesAndCurvatureOfExponentialSums.lean](../../../formal/GaloisForLFunctions/PrimeExponentialSums/ResonancesAndCurvatureOfExponentialSums.lean) | Check the revised norm identity in `pair_dispersion`. The last failure was the absolute value of the nonnegative weight. | [PrimeExponentialSums.lean](../../../formal/GaloisForLFunctions/PrimeExponentialSums.lean) |
| [ValuesInARestrictionFiber.lean](../../../formal/GaloisForLFunctions/HeckeLFunctions/Characters/ValuesInARestrictionFiber.lean) | Check the character-extension and evaluation multiplicities. The interrupted check has no recorded exit result. | [HeckeLFunctions.lean](../../../formal/GaloisForLFunctions/HeckeLFunctions.lean) |
| [FirstDetectionOfAnInvolution.lean](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/FiniteGroup/FirstDetectionOfAnInvolution.lean) | Check the power-fiber count in `parity_balance` and the first detecting depth in `exact_layer`. | [ArithmeticHarmonicAnalysis.lean](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis.lean) |
| [MeanCostOfTheHigherDyadicRanks.lean](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/FiniteGroup/MeanCostOfTheHigherDyadicRanks.lean) | Check the higher dyadic rank counts and the mean correction on coprime pairs. | [ArithmeticHarmonicAnalysis.lean](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis.lean) |
| [PrincipalRamanujanTransferOnTheDisk.lean](../../../formal/GaloisForLFunctions/PrimeExponentialSums/PrincipalRamanujanTransferOnTheDisk.lean) | Fix `hasSum_transfer`. Unfold the local abbreviation `x` in the power identity and match the cast of the natural prime power in the Ramanujan sum. Build its `.olean` for the disk-image and Gauss-gap modules. | [PrimeExponentialSums.lean](../../../formal/GaloisForLFunctions/PrimeExponentialSums.lean) |
| [ExactDiskImageOfThePrincipalTransfer.lean](../../../formal/GaloisForLFunctions/PrimeExponentialSums/ExactDiskImageOfThePrincipalTransfer.lean) | After the principal transfer builds, check its disk image, critical radius and radial extremum. | [PrimeExponentialSums.lean](../../../formal/GaloisForLFunctions/PrimeExponentialSums.lean) |
| [ConductorShellOfTheLocalGaussTransfer.lean](../../../formal/GaloisForLFunctions/PrimeExponentialSums/ConductorShellOfTheLocalGaussTransfer.lean) | Check the Fourier pullback and the primitive Gauss sum on its conductor shell. Build its `.olean` for the Gauss-gap module. | [PrimeExponentialSums.lean](../../../formal/GaloisForLFunctions/PrimeExponentialSums.lean) |
| [SharpGapBelowPrimitiveGaussTransfers.lean](../../../formal/GaloisForLFunctions/PrimeExponentialSums/SharpGapBelowPrimitiveGaussTransfers.lean) | After both the principal transfer and conductor shell build, check the primitive-energy criterion, product bound and dyadic equality case. | [PrimeExponentialSums.lean](../../../formal/GaloisForLFunctions/PrimeExponentialSums.lean) |

Five modules already compiled and are wired. Their latest source edits still need a file check.

- [AllDeterminantsOfACongruenceLattice.lean](../../../formal/GaloisForLFunctions/CollectiveDiophantineGeometry/AllDeterminantsOfACongruenceLattice.lean)
- [UnitFractionWitnessGram.lean](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/Divisors/UnitFractionWitnessGram.lean)
- [SignsAndPrincipalUnitsAtTwo.lean](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/FiniteGroup/SignsAndPrincipalUnitsAtTwo.lean)
- [VerticalFrequenciesOfAnIntegerLattice.lean](../../../formal/GaloisForLFunctions/CollectiveDiophantineGeometry/VerticalFrequenciesOfAnIntegerLattice.lean)
- [EdgePhasesOfAnIntegerCharge.lean](../../../formal/GaloisForLFunctions/HTGeometry/Quantum/EdgePhasesOfAnIntegerCharge.lean)


## Shared midpoint encoding on prime displacement planes (§2.5)

Wiring target is [CountingHolography.lean](../../../formal/GaloisForLFunctions/CountingHolography.lean): add both imports after `ReversibleCarryOnMixedSectionFamilies`.

| Lean file | Remaining work |
| --- | --- |
| [AdelicCarryOnSectionRepresentatives.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/AdelicCarryOnSectionRepresentatives.lean) | Source passed; its olean is built from the current source. Wire only. |
| [SharedMidpointEncodingOnPrimeDisplacementPlanes.lean](../../../formal/GaloisForLFunctions/CountingHolography/Sections/SharedMidpointEncodingOnPrimeDisplacementPlanes.lean) | Check the repairs from the last failed run: `padDivisor` coordinate lemmas, two-step `zsmul` simplification, the `Φ` additivity step, prime-tuple injectivity and cast steps, the submatrix index sum and the qualified `ArithmeticCastelnuovoSeveri.rightZeros`. The repaired source has not been checked. Fix any remaining errors, then wire. |

After the second file passes, move the [pipeline card](../../drafts/pipeline/2-fully-proven/adelic-midpoint-carry-on-prime-displacement-planes.md) to `3-formalized`.

## Two-interval quartet amplitude and ordinary-prime obstruction (§2.17)

Wiring targets are [ZeroConfigurationGeometry.lean](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry.lean) and [ExceptionalLayerTheory.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory.lean).

| Lean file | Remaining work | Umbrella to update |
| --- | --- | --- |
| [TwoIntervalAmplitudeAliasingAndCoprimeRealization.lean](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/TwoIntervalAmplitudeAliasingAndCoprimeRealization.lean) | Source passed with exit code 0 and its `.olean` is built from the current source. Wire only. | [ZeroConfigurationGeometry.lean](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry.lean) |
| [RemovingPrimeLogarithmsPreservesBothIntervalOscillations.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/RemovingPrimeLogarithmsPreservesBothIntervalOscillations.lean) | Source passed with exit code 0 and its `.olean` is built from the current source (required by `TwoIntervalQuartetAmplitudeAndOrdinaryPrimeObstruction.lean`). Wire only. | [ExceptionalLayerTheory.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory.lean) |
| [TwoAndThreeDilationRecurrencesAndSingleQuartetStratum.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TwoAndThreeDilationRecurrencesAndSingleQuartetStratum.lean) | Build its missing `.olean` (required by `MixingTwoPrimeDilationsRemovesQuartetAliasing.lean`). Already wired in `ExceptionalLayerTheory.lean`. | [ExceptionalLayerTheory.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory.lean) |
| [MixingTwoPrimeDilationsRemovesQuartetAliasing.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/MixingTwoPrimeDilationsRemovesQuartetAliasing.lean) | Build its `.olean` after `TwoAndThreeDilationRecurrencesAndSingleQuartetStratum.olean` exists (required by `TwoIntervalQuartetAmplitudeAndOrdinaryPrimeObstruction.lean`), then wire. | [ExceptionalLayerTheory.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory.lean) |
| [TwoIntervalQuartetAmplitudeAndOrdinaryPrimeObstruction.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TwoIntervalQuartetAmplitudeAndOrdinaryPrimeObstruction.lean) | Complete `sorry`-free source written; dependency `.olean`s for `TwoIntervalAmplitudeAliasingAndCoprimeRealization`, `QuadratureOfTwoConsecutivePrimeIntervals`, `RemovingPrimeLogarithmsPreservesBothIntervalOscillations`, and `TwoProperPowerWavesCharacterizeASingleQuartet` are already built. After `TwoAndThreeDilationRecurrencesAndSingleQuartetStratum.olean` and `MixingTwoPrimeDilationsRemovesQuartetAliasing.olean` are built, check the file, fix any errors, and wire. | [ExceptionalLayerTheory.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory.lean) |

After [TwoIntervalQuartetAmplitudeAndOrdinaryPrimeObstruction.lean](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TwoIntervalQuartetAmplitudeAndOrdinaryPrimeObstruction.lean) passes, move the [pipeline card](../../drafts/pipeline/2-fully-proven/review-1811-2-17-two-interval-quartet-amplitude.md) to `3-formalized`.
