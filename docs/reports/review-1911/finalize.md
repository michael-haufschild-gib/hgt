## §2.11 Quantitative factorization with signed boundaries

All listed §2.11 modules compile and are wired. The bounded-stretch matching pairs every squarefree integer greater than one by a one-to-two prime exchange. Each partner is at most eight times the original integer. [Bounded-stretch theorem](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/BoundedStretchForPerfectRestrictedMatchings.lean) · [Umbrella](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus.lean)

All five modules for stopping depth and critical smooth counts compile and are wired, through [TheSecondCoefficientAtTheLogSquareWall](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheSecondCoefficientAtTheLogSquareWall.lean).

The moving-cutoff and least-prime modules compile and are wired. The head-variation bound follows from the existing square-crossing estimate at the squares of the two heights. [PrimeArrivalsAtAMovingLogSquareWall](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/PrimeArrivalsAtAMovingLogSquareWall.lean) · [TheExactFlowAcrossLeastPrimeBranches](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheExactFlowAcrossLeastPrimeBranches.lean)

**Scope.** The two donor modules cover the paper arguments for donor supply and reversible switches. Attainment by the full prescribed-smaller-prime matching remains conjectural. The whole-window semiprime flux, the proposed natural-wall variation constant, and the square-root bound on the recombined interior also remain open.

The two cofactor-range modules compile and are wired. [OneCofactorAtEveryDyadicQuotient](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/OneCofactorAtEveryDyadicQuotient.lean) · [TheStripSeenThroughAnArbitrarilyShortCofactorRange](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheStripSeenThroughAnArbitrarilyShortCofactorRange.lean).

## Cubic fields, scattering and quantum heating

All 117 started modules compile and are wired. These include the four-shot cubic minimax bounds, sparse velocity recovery, and the real factorization of the scattering polynomial.

All six quantum-heating modules compile and are wired, through the sharp one- and two-channel sampling thresholds in [SchwartzHeatingSampling](../../../formal/GaloisForLFunctions/HTGeometry/QuantumChannels/SchwartzHeatingSampling.lean).

## §2.18 Prime midpoint formalization

All nine listed modules compile and are wired. The cubic triple-price difference equals the difference of the two sharp prime boxes. Both power-grid floor costs have logarithmic coefficient one half. The fourth-root cutoff gives an error of order $n^{1/2+ε}$ for every $ε>0$. The Mellin transform of the signed midpoint weight under a common random dilation equals the stated dyadic multiplier. [Triple boxes](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeCountsInTheTwoMidpointTripleBoxes.lean) · [Floor costs](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheAccumulatedFloorOnPowerSampledPrimeOctaves.lean) · [Fourth-root estimate](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheSmoothFactorAtTheFourthRootMidpoint.lean) · [Mellin identity](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheMellinMultiplierOfTheSmoothPrimeMidpoint.lean)

## Remaining Lean drafts from the paper proofs

29 of 34 drafts compile and are wired. The five below still need a successful Lean check and an import in their respective umbrellas.

| Module | Remaining work |
| --- | --- |
| [TheHarmonicCostOfHolesInAWeilComb](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/TheHarmonicCostOfHolesInAWeilComb.lean) | Row inequality, log-product rewrite and image-sum fixes are in place. The check was interrupted. Check and wire into `SignedArithmeticCorrespondences.lean`. |
| [TheFinitePartOfAShortFlatWeilComb](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/TheFinitePartOfAShortFlatWeilComb.lean) | Fixed the local error-term rewrite in `mesoscopic_flat_comb_limit`. Check and wire into `SignedArithmeticCorrespondences.lean`. |
| [ParitySectorMomentsAtTheUnitaryMidpoint](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ParitySectorMomentsAtTheUnitaryMidpoint.lean) | In `ExceptionalLayerTheory/SquareConductors/`, build missing oleans for `TheNegativeRankFiveMidpoint` and `RealizingTheUnitaryMidpointChambers`, then `EveryValueOfTheFivePrimeMidpoint`. Check the draft and wire into `ExceptionalLayerTheory.lean`. |
| [TheMobiusReadingOfTheScatteringReturns](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TailEnergy/TheMobiusReadingOfTheScatteringReturns.lean) | Build the missing olean for sibling module `PrimePowerReturnsForceSignedCancellation`. Check the draft and wire into `BlackHoleRingdown.lean`. |
| [TheTensorPowersOfAPermutationCharacter](../../../formal/GaloisForLFunctions/RepresentationLifting/KTheory/TheTensorPowersOfAPermutationCharacter.lean) | Build the missing olean for sibling module `PermutationVirtualFreeness`. Check the draft and wire into `RepresentationLifting.lean`. |

## Remaining prime-cut, prime-excursion, and analytic modules

Paths are relative to `formal/GaloisForLFunctions/`. Each row lists the remaining check, dependency build, or umbrella import.

| Directory | Module | Remaining work |
| --- | --- | --- |
| `ExceptionalLayerTheory/SquareConductors` | `ThinningThePowerSamplesOfTheReciprocalPrimeOctave` | The parse error in `reciprocal_deficit_le_gcd` was fixed. The check was interrupted. Check and wire into `ExceptionalLayerTheory.lean`. |
| `ExceptionalLayerTheory/SquareConductors` | `TheFactorialCenterOfTheSmallUnitaryDivisors` | Check the revised reindexing proof. Already wired. |
| `ExclusionOfTheCriticalState/Wall` | `ReciprocalWeightDistortionOnJointPrimeExcursions` | Check the corrected covariance proof and affine regression identity. Wire into `ExclusionOfTheCriticalState.lean`. |
| `ExclusionOfTheCriticalState/Wall` | `OneSuperlevelOfTheOppositePrimeMoment`, `TheFlankContrastInTheOppositePrimeMoment` | Check both and wire into `ExclusionOfTheCriticalState.lean`. |
| `ExclusionOfTheCriticalState/Wall` | `UniformCancellationOnTruncatedOddQuotientIntervals` → `ThePowerSavingOnEveryOddQuotientDenominatorInterval` → `TheDiagonalCutoffForSquareRootNormalizedPrimeExcursions` | Build the first two missing oleans in order, then check the third module. Wire all three into `ExclusionOfTheCriticalState.lean`. |
| `HTGeometry/DispersivePDE` | `TheGrossPitaevskiiCorrectorOfTheKdVPulse` → `TheDensityShearOfAGreyGrossPitaevskiiSoliton` | Build the corrector’s missing olean, including the new peak-location proof. The corrector is wired. Check the density-shear module and wire it into `HTGeometry/DispersivePDE/Applications.lean`. |
| `CompactHyperbolicSurfaces` | `LogarithmicDistortionOfAutomorphicKernels` | Check finite-radius attainment and fixed-displacement sharpness. Already wired. |
| `ArithmeticAuxiliaryDynamics/Spectrum` | `TheHardyEnergyOfFloorExcessTails` | Check the added remaining-capacity identity and factor-two bound. Already wired. |
| `GaloisTheoryOfZeros/Analysis` | `TwoFocusBoundsForTheUnshiftedJensenPolynomials`, `TheGeometricMeanOfAHeatBoundaryDiscriminant` | Check both and wire into `GaloisTheoryOfZeros.lean`. The heat-window dependency now has an olean. |
| `GaloisTheoryOfZeros` | `OneRationalHeightComparisonPerJensenDegree` → `ErrorsAndDensitiesInTheScheduledJensenTest` | Build the missing olean for the already checked and wired comparison. Check the scheduled test and wire it into `GaloisTheoryOfZeros.lean`. |
| `BlackHoleRingdown/TailEnergy` | `QuadraticPhaseRecoveryOfTheCompleteReceiverMatrix` | Check and wire into `BlackHoleRingdown.lean`. Its phase-sweep dependency is built and wired. |

## Remaining midpoint and collision proofs

Of 63 started modules in this group, 56 compile and are wired. The seven below still need a successful Lean check and an umbrella import.

| Module | Remaining work |
| --- | --- |
| [AllScaleFractionalReconstructionOfThePrimePrice](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/AllScaleFractionalReconstructionOfThePrimePrice.lean) | Check and wire into `ExceptionalLayerTheory.lean`. Both imported project modules have oleans. |
| [ConsecutiveRootScalesOfTheBalancedCompositePrice](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ConsecutiveRootScalesOfTheBalancedCompositePrice.lean) | Check and wire into `ExceptionalLayerTheory.lean`. |
| [CountingTheWidthsOfGcdExcursions](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/CountingTheWidthsOfGcdExcursions.lean) | Check was interrupted. Resume the check and wire into `ExceptionalLayerTheory.lean`. |
| [RecoveringThePrimeMidpointFromConductorCuts](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/RecoveringThePrimeMidpointFromConductorCuts.lean) | Build missing sibling oleans in order, first `TheFirstMomentSeenByTheIntegratedConductorSpline`, then `TheVariationOfTheMovingPrimeCut`. Check and wire into `ExceptionalLayerTheory.lean`. |
| [TheThreeFiniteLimitsOfAnOrdinaryPrimeMidpointStep](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheThreeFiniteLimitsOfAnOrdinaryPrimeMidpointStep.lean) | Check and wire into `ExceptionalLayerTheory.lean`. |
| [TheZeroAbscissaSeenOnLongPrimePlateaus](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheZeroAbscissaSeenOnLongPrimePlateaus.lean) | Check the cast fix in `midpoint_bound_from_mesh` and wire into `ExceptionalLayerTheory.lean`. Its signed-sampling dependency is built. |
| [TheCyclicSpectrumOfTheCollisionMoments](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/Analysis/TheCyclicSpectrumOfTheCollisionMoments.lean) | Build the missing `InfiniteRankWeilTheory/TheRankBarrier.olean`. The lower-discriminant dependency is built. Check and wire into `GaloisTheoryOfZeros.lean`. |

## Remaining modules from the Mertens, xi, scattering and arithmetic drafts

68 of 151 started modules still need a successful Lean check and an umbrella import. Eight additional dependencies need a missing `.olean`.

The check of `MertensExcursionsAtEveryLargeCutoff` was interrupted after fixing a missing closing parenthesis in `mertens_mass_two_population_bound` and specifying the real exponent in `eventually_many_mertens_excursions`. Its dependency `TheAccumulatedMertensSquareSeesTheZeroWidth` is built.

### Missing dependency artifacts

| Source | Remaining work | Needed by |
| --- | --- | --- |
| [LevelWidthsOfAReflectedHadamardPair](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/LevelWidthsOfAReflectedHadamardPair.lean) | Build `.olean`. | `InferringAReflectedPairFromTwoLevelEdges` |
| [TheFirstMomentSeenByTheIntegratedConductorSpline](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheFirstMomentSeenByTheIntegratedConductorSpline.lean) | Build `.olean`. | `TheVariationOfTheMovingPrimeCut` |
| [TheLogarithmicCorrectionToGaussianObservation](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLogarithmicCorrectionToGaussianObservation.lean) | Build `.olean`. | `SeparationOfTwoGaussianModesAtHighObservationHeight` |
| [OppositeExcursionsOfTheThirdConfinedPrimeWave](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/OppositeExcursionsOfTheThirdConfinedPrimeWave.lean) | Build `.olean`. | `BothSignsInOneGammaAverageOfTheThirdPrimeWave` |
| [HermiteConstantsOfTheHeatMinors](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/Analysis/HermiteConstantsOfTheHeatMinors.lean) | Build `.olean`. Wire into `GaloisTheoryOfZeros.lean`. | `ThreeBoundaryMomentsDetectEveryHeatCollision` |
| [MultiplicityStrataOfTheHeatWinding](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/Analysis/MultiplicityStrataOfTheHeatWinding.lean) | Build `.olean`. | `TheAreaExcessOfSimultaneousHeatCollisions` |
| [RecoveringHeatTimeFromOneReflectedPair](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/Analysis/RecoveringHeatTimeFromOneReflectedPair.lean) | Build `.olean`. | `ExactlyWhichHeatPairsHaveAMidpointReadFromTheirGap` |
| [ThreeBoundaryMomentsDetectEveryHeatCollision](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/Analysis/ThreeBoundaryMomentsDetectEveryHeatCollision.lean) | Build `.olean` after `HermiteConstantsOfTheHeatMinors`. Wire into `GaloisTheoryOfZeros.lean`. | `CollisionOrdersFromAreasOfTheHeatBoundaryMinors` |

### Unfinished proofs

Each table names its umbrella. Build rows need an `.olean` for a listed importer. Check rows need a direct Lean check. Wire each module after it passes.

#### [ArithmeticContinuationAndCriticalEnergy](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy.lean)

| Module | Action | Missing imports to build first |
| --- | --- | --- |
| [TheHalfEndpointChargeOfADilatedLattice](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheHalfEndpointChargeOfADilatedLattice.lean) | Build | — |

#### [ArithmeticCountingPositivity](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity.lean)

| Module | Action | Missing imports to build first |
| --- | --- | --- |
| [TwoSquarefreeTranslatesInShortIntervals](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/TwoSquarefreeTranslatesInShortIntervals.lean) | Check | — |

#### [ArithmeticPositiveDuality](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality.lean)

| Module | Action | Missing imports to build first |
| --- | --- | --- |
| [TheRangeOfGreedyPrimeDeletions](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheRangeOfGreedyPrimeDeletions.lean) | Check | — |

#### [BlackHoleRingdown](../../../formal/GaloisForLFunctions/BlackHoleRingdown.lean)

| Module | Action | Missing imports to build first |
| --- | --- | --- |
| [CarrierFrequenciesThatMissNoResonance](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TailEnergy/CarrierFrequenciesThatMissNoResonance.lean) | Build | — |
| [ReadingAPulseFromItsDerivativeEnergy](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TailEnergy/ReadingAPulseFromItsDerivativeEnergy.lean) | Build | — |
| [ResonancesOfTwoSimultaneousReceiverSweeps](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TailEnergy/ResonancesOfTwoSimultaneousReceiverSweeps.lean) | Build | — |
| [SpectraOfCascadedRectangularWindows](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TailEnergy/SpectraOfCascadedRectangularWindows.lean) | Build | — |
| [TheMomentPulsesOfAFlatWindow](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TailEnergy/TheMomentPulsesOfAFlatWindow.lean) | Build | — |
| [ASingleCompactPulseDetectsEveryStrip](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TailEnergy/ASingleCompactPulseDetectsEveryStrip.lean) | Build | `CarrierFrequenciesThatMissNoResonance`, `ReadingAPulseFromItsDerivativeEnergy` |
| [AZeroSetForTheDyadicSincPulse](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TailEnergy/AZeroSetForTheDyadicSincPulse.lean) | Build | `SpectraOfCascadedRectangularWindows` |
| [AllMomentsOfARapidReceiverSweep](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TailEnergy/AllMomentsOfARapidReceiverSweep.lean) | Check | `ResonancesOfTwoSimultaneousReceiverSweeps` |
| [ExponentialTypeOfCascadedTimeWindows](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TailEnergy/ExponentialTypeOfCascadedTimeWindows.lean) | Build | `SpectraOfCascadedRectangularWindows` |
| [AccumulatingCarriersForceTheScatteringStrip](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TailEnergy/AccumulatingCarriersForceTheScatteringStrip.lean) | Check | `ASingleCompactPulseDetectsEveryStrip` |
| [FourExplicitPulsesDetectEveryScatteringStrip](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TailEnergy/FourExplicitPulsesDetectEveryScatteringStrip.lean) | Check | `TheMomentPulsesOfAFlatWindow`, `ASingleCompactPulseDetectsEveryStrip` |
| [OnePulseEnergyForcesItsOwnBlindFrequencies](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TailEnergy/OnePulseEnergyForcesItsOwnBlindFrequencies.lean) | Build | `ASingleCompactPulseDetectsEveryStrip` |
| [TheExactTypeOfAWindowSpectrum](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TailEnergy/TheExactTypeOfAWindowSpectrum.lean) | Build | `ExponentialTypeOfCascadedTimeWindows`, `AZeroSetForTheDyadicSincPulse` |
| [TheSteklovPulseSeesEveryScatteringPole](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TailEnergy/TheSteklovPulseSeesEveryScatteringPole.lean) | Build | `SpectraOfCascadedRectangularWindows`, `OnePulseEnergyForcesItsOwnBlindFrequencies` |
| [TheSupportEndpointsOfTheSteklovPulse](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TailEnergy/TheSupportEndpointsOfTheSteklovPulse.lean) | Check | `TheExactTypeOfAWindowSpectrum`, `TheSteklovPulseSeesEveryScatteringPole` |

#### [ConjugateDiagonalGeometry](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry.lean)

| Module | Action | Missing imports to build first |
| --- | --- | --- |
| [MertensExcursionsAtEveryLargeCutoff](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/MertensExcursionsAtEveryLargeCutoff.lean) | Resume check | — |

#### [ExceptionalLayerTheory](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory.lean)

| Module | Action | Missing imports to build first |
| --- | --- | --- |
| [CountingEachMultiplicityWithoutLocatingTheZeros](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CountingEachMultiplicityWithoutLocatingTheZeros.lean) | Check | — |
| [CountingEveryZeroOrderByChangingTheAperture](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CountingEveryZeroOrderByChangingTheAperture.lean) | Check | — |
| [DilationsOfTheEighthPowerGcdDeficit](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/DilationsOfTheEighthPowerGcdDeficit.lean) | Check | — |
| [FiniteDerivativeSchedulesAdmitDisjointMultiplicityHistograms](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/FiniteDerivativeSchedulesAdmitDisjointMultiplicityHistograms.lean) | Check | — |
| [FirstPassageOfTheEighthPowerGcdShortfall](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/FirstPassageOfTheEighthPowerGcdShortfall.lean) | Build | — |
| [HarmonicPhasesOfTheEighthPowerShortfall](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/HarmonicPhasesOfTheEighthPowerShortfall.lean) | Check | — |
| [OneLogarithmicDerivativeOrderReadsTheXiHistogram](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/OneLogarithmicDerivativeOrderReadsTheXiHistogram.lean) | Build | — |
| [PowerDiscountsOfTheGcdShortfall](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/PowerDiscountsOfTheGcdShortfall.lean) | Check | — |
| [RecoveringAPoleByBarycentricInterpolation](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/RecoveringAPoleByBarycentricInterpolation.lean) | Build | — |
| [TheCountWithSmallProductOfSimplePrimeFactors](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheCountWithSmallProductOfSimplePrimeFactors.lean) | Build | — |
| [TheCountingExponentOfDeletedPrimePowers](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheCountingExponentOfDeletedPrimePowers.lean) | Check | — |
| [TheDirichletPoleOfTheEighthPowerShortfall](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheDirichletPoleOfTheEighthPowerShortfall.lean) | Check | — |
| [TheDistributionOfAccumulatedGcdShortfall](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheDistributionOfAccumulatedGcdShortfall.lean) | Check | — |
| [TheExactBadHeightsOfHorizontalHadamardTests](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheExactBadHeightsOfHorizontalHadamardTests.lean) | Check | — |
| [TheFiniteHorizonProfileOfProperPrimePowers](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheFiniteHorizonProfileOfProperPrimePowers.lean) | Build | — |
| [TheFourthOrderEvenHorizonShortfall](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheFourthOrderEvenHorizonShortfall.lean) | Check | — |
| [TheHeightErrorOfTheHadamardThreshold](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheHeightErrorOfTheHadamardThreshold.lean) | Build | — |
| [TheOptimalSpacingOfFourHadamardReadings](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheOptimalSpacingOfFourHadamardReadings.lean) | Build | — |
| [ThePolynomialWeightsOfTheXiDivisor](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/ThePolynomialWeightsOfTheXiDivisor.lean) | Build | — |
| [TwoSpacingsOfTheExceptionalPrimeFilter](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TwoSpacingsOfTheExceptionalPrimeFilter.lean) | Check | — |
| [WhatTheThirdDerivativeAreaSees](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/WhatTheThirdDerivativeAreaSees.lean) | Check | — |
| [AlternatingCornersOfTheProperPowerHorizon](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/AlternatingCornersOfTheProperPowerHorizon.lean) | Build | `TheFiniteHorizonProfileOfProperPrimePowers` |
| [AnExplicitPrecisionForOneDerivativeArea](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/AnExplicitPrecisionForOneDerivativeArea.lean) | Check | `OneLogarithmicDerivativeOrderReadsTheXiHistogram` |
| [InferringAReflectedPairFromTwoLevelEdges](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/InferringAReflectedPairFromTwoLevelEdges.lean) | Check | `LevelWidthsOfAReflectedHadamardPair` |
| [ReadingXiMultiplicityFromArbitraryNearbySites](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/ReadingXiMultiplicityFromArbitraryNearbySites.lean) | Build | `RecoveringAPoleByBarycentricInterpolation` |
| [SeparationOfTwoGaussianModesAtHighObservationHeight](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SeparationOfTwoGaussianModesAtHighObservationHeight.lean) | Build | `TheLogarithmicCorrectionToGaussianObservation` |
| [TheComplexPowerSumsOfTheXiDivisorFromFourAreas](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheComplexPowerSumsOfTheXiDivisorFromFourAreas.lean) | Check | `ThePolynomialWeightsOfTheXiDivisor` |
| [TheMeasureOfNegativeHadamardReadings](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheMeasureOfNegativeHadamardReadings.lean) | Check | `TheHeightErrorOfTheHadamardThreshold` |
| [ThePowerMomentsOfEighthGridDiscrepancy](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePowerMomentsOfEighthGridDiscrepancy.lean) | Check | `FirstPassageOfTheEighthPowerGcdShortfall`, `RealOrdersOfPerturbedPowerTails` |
| [TheSimplePrimeFactorsRequiredAtTheCompositeMidpoint](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheSimplePrimeFactorsRequiredAtTheCompositeMidpoint.lean) | Check | `TheCountWithSmallProductOfSimplePrimeFactors` |
| [TheVariationOfTheMovingPrimeCut](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheVariationOfTheMovingPrimeCut.lean) | Build | `TheFirstMomentSeenByTheIntegratedConductorSpline` |
| [WhichMultiplicitiesOnePrimeRadicalAreaIdentifies](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/WhichMultiplicitiesOnePrimeRadicalAreaIdentifies.lean) | Check | `OneLogarithmicDerivativeOrderReadsTheXiHistogram` |
| [FourHorizontalSitesDetermineTheXiMultiplicity](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/FourHorizontalSitesDetermineTheXiMultiplicity.lean) | Check | `ReadingXiMultiplicityFromArbitraryNearbySites`, `TheOptimalSpacingOfFourHadamardReadings` |
| [NoncancellationOfAGaussianZeroQuartet](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/NoncancellationOfAGaussianZeroQuartet.lean) | Check | `SeparationOfTwoGaussianModesAtHighObservationHeight` |
| [TheConstantTermOfTheProperPowerHorizon](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheConstantTermOfTheProperPowerHorizon.lean) | Check | `AlternatingCornersOfTheProperPowerHorizon`, `TheHalfEndpointChargeOfADilatedLattice` |

#### [ExclusionOfTheCriticalState](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState.lean)

| Module | Action | Missing imports to build first |
| --- | --- | --- |
| [CountingSimultaneousPrimeExcursionsAtOneLevel](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/CountingSimultaneousPrimeExcursionsAtOneLevel.lean) | Check | — |
| [MovingOrdinateBandsOfAFiniteLayer](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/MovingOrdinateBandsOfAFiniteLayer.lean) | Check | — |
| [BothSignsInOneGammaAverageOfTheThirdPrimeWave](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/BothSignsInOneGammaAverageOfTheThirdPrimeWave.lean) | Check | `OppositeExcursionsOfTheThirdConfinedPrimeWave` |

#### [FamilyContinuationTheory](../../../formal/GaloisForLFunctions/FamilyContinuationTheory.lean)

| Module | Action | Missing imports to build first |
| --- | --- | --- |
| [ChordBoundsForMellinReadingsOnTheSecondLine](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/ChordBoundsForMellinReadingsOnTheSecondLine.lean) | Build | — |
| [TheCubicProbeOnAThreeHalvesPowerMesh](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheCubicProbeOnAThreeHalvesPowerMesh.lean) | Check | `ChordBoundsForMellinReadingsOnTheSecondLine` |

#### [GaloisTheoryOfZeros](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros.lean)

| Module | Action | Missing imports to build first |
| --- | --- | --- |
| [DilationRatiosOfTheHeatBoundaryDiscriminant](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/Analysis/DilationRatiosOfTheHeatBoundaryDiscriminant.lean) | Check | — |
| [TheFullParabolicRayJetOfTheHeatFamily](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/Analysis/TheFullParabolicRayJetOfTheHeatFamily.lean) | Build | — |
| [ExactlyWhichHeatPairsHaveAMidpointReadFromTheirGap](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/Analysis/ExactlyWhichHeatPairsHaveAMidpointReadFromTheirGap.lean) | Build | `RecoveringHeatTimeFromOneReflectedPair` |
| [TheAreaExcessOfSimultaneousHeatCollisions](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/Analysis/TheAreaExcessOfSimultaneousHeatCollisions.lean) | Check | `MultiplicityStrataOfTheHeatWinding` |
| [TheCommonDriftOfAllSheetsAtAHeatCollision](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/Analysis/TheCommonDriftOfAllSheetsAtAHeatCollision.lean) | Build | `TheFullParabolicRayJetOfTheHeatFamily` |
| [CollisionOrdersFromAreasOfTheHeatBoundaryMinors](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/Analysis/CollisionOrdersFromAreasOfTheHeatBoundaryMinors.lean) | Check | `ThreeBoundaryMomentsDetectEveryHeatCollision` |
| [TheMidpointResponseOfAnUnorderedHeatPair](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/Analysis/TheMidpointResponseOfAnUnorderedHeatPair.lean) | Check | `TheCommonDriftOfAllSheetsAtAHeatCollision`, `ExactlyWhichHeatPairsHaveAMidpointReadFromTheirGap` |

#### [Hurwitz](../../../formal/GaloisForLFunctions/Hurwitz.lean)

| Module | Action | Missing imports to build first |
| --- | --- | --- |
| [RealOrdersOfPerturbedPowerTails](../../../formal/GaloisForLFunctions/Hurwitz/RealOrdersOfPerturbedPowerTails.lean) | Build | — |

#### [SignedArithmeticCorrespondences](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences.lean)

| Module | Action | Missing imports to build first |
| --- | --- | --- |
| [TheParityMinorsOfTheCompleteWeilComb](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/TheParityMinorsOfTheCompleteWeilComb.lean) | Check | — |

## Remaining cofactor, squarefree, prime-contact and heat manuscripts

53 drafts still need a successful Lean check and an import in their chapter umbrella. **Build** produces a missing `.olean` used by another draft. **Check** needs only the individual file check. Each link points to its source.

In `TheSmoothDensityReadByTheRelativeSignRadius`, the nested absolute-value syntax in `stable_ratio` was corrected. Its build was interrupted before a result. The imported `TheRobustSignRadiusOfTheFirstRoughPrimeBand.olean` is present.

| Chapter umbrella | Drafts to wire | Action | Missing imports to build first |
| --- | --- | --- | --- |
| [ArithmeticAuxiliaryDynamics](../../../formal/GaloisForLFunctions/ArithmeticAuxiliaryDynamics.lean) | [DivisorJumpStability](../../../formal/GaloisForLFunctions/ArithmeticAuxiliaryDynamics/Spectrum/DivisorJumpStability.lean) | Check | — |
| [BezoutValuationIncidence](../../../formal/GaloisForLFunctions/BezoutValuationIncidence.lean) | [GramOfThePrimeSquarefreeDifferences](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/Sieve/GramOfThePrimeSquarefreeDifferences.lean) · [TheCostOfDeletingPrimesFromSquarefreeCounts](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/Sieve/TheCostOfDeletingPrimesFromSquarefreeCounts.lean) | Check | — |
| [BlackHoleRingdown](../../../formal/GaloisForLFunctions/BlackHoleRingdown.lean) | [SectorEnergyMultiplier](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TailEnergy/SectorEnergyMultiplier.lean) | Check | `PrimePowerReturnsForceSignedCancellation` |
| [ConjugateDiagonalGeometry](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry.lean) | [ACubeRootGapForConsecutiveSquarefreePairs](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/ACubeRootGapForConsecutiveSquarefreePairs.lean) · [PhaseRetrievalFromWideWindowSlopes](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/PhaseRetrievalFromWideWindowSlopes.lean) · [TheRegularPartOfSquarefreeSections](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/TheRegularPartOfSquarefreeSections.lean) | Build | — |
| [ConjugateDiagonalGeometry](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry.lean) | [TheEndpointFormOfTheMoebiusMean](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/TheEndpointFormOfTheMoebiusMean.lean) | Build | `TheSharpHolderExponentForInfiniteGramRecovery` |
| [ConjugateDiagonalGeometry](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry.lean) | [TheMicroscopicCovarianceOfSharpMoebiusSections](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/TheMicroscopicCovarianceOfSharpMoebiusSections.lean) | Build | `TheEndpointFormOfTheMoebiusMean` |
| [ConjugateDiagonalGeometry](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry.lean) | [ShortSectionsInsideLongCriticalMeans](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/ShortSectionsInsideLongCriticalMeans.lean) | Build | `TheSharpHolderExponentForInfiniteGramRecovery`, `TheEndpointFormOfTheMoebiusMean` |
| [ConjugateDiagonalGeometry](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry.lean) | [DriftingCriticalPrefixes](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/DriftingCriticalPrefixes.lean) · [DyadicPhaseSelection](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/DyadicPhaseSelection.lean) · [SuperpolynomialMobiusOrder](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/SuperpolynomialMobiusOrder.lean) · [ThePackingOrderOfOneSignMertensIntervals](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/ThePackingOrderOfOneSignMertensIntervals.lean) | Check | — |
| [ConjugateDiagonalGeometry](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry.lean) | [AdmissibleLongMomentExponents](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/AdmissibleLongMomentExponents.lean) | Check | `ShortSectionsInsideLongCriticalMeans` |
| [ConjugateDiagonalGeometry](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry.lean) | [AnchoredBandwidth](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/AnchoredBandwidth.lean) | Check | `TheSharpHolderExponentForInfiniteGramRecovery` |
| [ConjugateDiagonalGeometry](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry.lean) | [JetsOfDyadicSquarefreeSections](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/JetsOfDyadicSquarefreeSections.lean) · [OptimalHarmonicRecoveryOfTheSquarefreeLaurentGerm](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/OptimalHarmonicRecoveryOfTheSquarefreeLaurentGerm.lean) | Check | `TheRegularPartOfSquarefreeSections` |
| [ConjugateDiagonalGeometry](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry.lean) | [OptimalReadingsForOneMoreCoefficient](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/OptimalReadingsForOneMoreCoefficient.lean) | Check | `PhaseRetrievalFromWideWindowSlopes` |
| [ConjugateDiagonalGeometry](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry.lean) | [OrthogonalHeightsOfTheSharpMoebiusSections](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/OrthogonalHeightsOfTheSharpMoebiusSections.lean) | Check | `TheMicroscopicCovarianceOfSharpMoebiusSections` |
| [ConjugateDiagonalGeometry](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry.lean) | [FourFoldedReadings](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/FourFoldedReadings.lean) | Check | `TheFoldedReadoutOfAMoebiusWindow`, `PhaseRetrievalFromWideWindowSlopes` |
| [ConjugateDiagonalGeometry](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry.lean) | [SquarefreeDyadicCovariance](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/SquarefreeDyadicCovariance.lean) | Check | `TheMicroscopicCovarianceOfSharpMoebiusSections`, `TheRegularPartOfSquarefreeSections` |
| [ConjugateDiagonalGeometry](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry.lean) | [TheAgeExpansionOfTheFirstSquarefreeBandwidth](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/TheAgeExpansionOfTheFirstSquarefreeBandwidth.lean) | Check | `TheHalfIntegerLimitsOfTheFirstSquarefreeBandwidth`, `ACubeRootGapForConsecutiveSquarefreePairs` |
| [ExceptionalLayerTheory](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory.lean) | [RecoveringPrimePairsFromTranslatedMidpoints](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/RecoveringPrimePairsFromTranslatedMidpoints.lean) | Build | `TheOddFourierModesOfTheSharpPrimeMidpoint` |
| [ExceptionalLayerTheory](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory.lean) | [DampingMinimum](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/DampingMinimum.lean) | Check | — |
| [ExceptionalLayerTheory](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory.lean) | [ConductorSensitivity](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ConductorSensitivity.lean) | Check | `TheFirstMomentSeenByTheIntegratedConductorSpline` |
| [ExceptionalLayerTheory](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory.lean) | [MidpointPrimePairVariation](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/MidpointPrimePairVariation.lean) | Check | `RecoveringPrimePairsFromTranslatedMidpoints` |
| [ExclusionOfTheCriticalState](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState.lean) | [CriticalHeatProfile](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/CriticalHeatProfile.lean) · [GeometricWallShells](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/GeometricWallShells.lean) · [PrimeRectangles](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/PrimeRectangles.lean) | Check | — |
| [ExclusionOfTheCriticalState](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState.lean) | [CoalescingHeatRates](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/CoalescingHeatRates.lean) | Check | `TheMellinHeatMomentsOfTheOrdinateTail` |
| [ExclusionOfTheCriticalState](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState.lean) | [ConfinedLaplaceSaddle](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/ConfinedLaplaceSaddle.lean) | Check | `BothSignsInOneGammaAverageOfTheThirdPrimeWave` |
| [FamilyContinuationTheory](../../../formal/GaloisForLFunctions/FamilyContinuationTheory.lean) | [CubicDyadicSampling](../../../formal/GaloisForLFunctions/FamilyContinuationTheory/CubicDyadicSampling.lean) | Check | — |
| [FiniteFreeProbability](../../../formal/GaloisForLFunctions/FiniteFreeProbability.lean) | [JensenDegreeExpansion](../../../formal/GaloisForLFunctions/FiniteFreeProbability/Composition/JensenDegreeExpansion.lean) | Check | — |
| [GaloisTheoryOfZeros](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros.lean) | [TheCubicDisplacementOfTheHeatSheets](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/Analysis/TheCubicDisplacementOfTheHeatSheets.lean) | Check | `TheCommonDriftOfAllSheetsAtAHeatCollision` |
| [MultiplicativePositivityGeometry](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry.lean) | [CollapsedPrimeSites](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/CollapsedPrimeSites.lean) · [SpreadingPrimeGramMassOnTwoLogarithmicSteps](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/SpreadingPrimeGramMassOnTwoLogarithmicSteps.lean) · [ThreeSiteCrossover](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/ThreeSiteCrossover.lean) | Check | `TheEquilibriumOfTheThreeSitePrimeGram` |
| [PrimeTorusTheory](../../../formal/GaloisForLFunctions/PrimeTorusTheory.lean) | [SignedTraces](../../../formal/GaloisForLFunctions/PrimeTorusTheory/Resonators/SignedTraces.lean) | Check | `TheUnitCrossingsOfThreePrimePhases` |
| [RestrictedFactorizationCalculus](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus.lean) | [TheSmoothDensityReadByTheRelativeSignRadius](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheSmoothDensityReadByTheRelativeSignRadius.lean) | Build | — |
| [RestrictedFactorizationCalculus](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus.lean) | [UniformlyTiltingTheEulerPriceAtOne](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/UniformlyTiltingTheEulerPriceAtOne.lean) | Check | — |
| [RestrictedFactorizationCalculus](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus.lean) | [TheUniformErasureThresholdOfPolynomialPrimeBands](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheUniformErasureThresholdOfPolynomialPrimeBands.lean) | Check | `TheSmoothDensityReadByTheRelativeSignRadius` |
| [SignedArithmeticCorrespondences](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences.lean) | [TheJointKernelOfThePrimeRaySums](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/TheJointKernelOfThePrimeRaySums.lean) | Build | — |
| [SignedArithmeticCorrespondences](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences.lean) | [CountingTheTrianglesOfThePrimeContactMatrix](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/CountingTheTrianglesOfThePrimeContactMatrix.lean) | Build | `TheFirstOddMomentOfThePrimeContactMatrix` |
| [SignedArithmeticCorrespondences](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences.lean) | [TheFirstOddMomentOfThePrimeContactMatrix](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/TheFirstOddMomentOfThePrimeContactMatrix.lean) | Build | `TheIsolatedSitesOfThePrimeContactMatrix` |
| [SignedArithmeticCorrespondences](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences.lean) | [PrimeContactPathsBeforeTheFirstSquare](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/PrimeContactPathsBeforeTheFirstSquare.lean) · [PrimeCutSpectrum](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/PrimeCutSpectrum.lean) · [TheKernelFiltrationOfDirectedPrimeContacts](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/TheKernelFiltrationOfDirectedPrimeContacts.lean) | Check | — |
| [SignedArithmeticCorrespondences](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences.lean) | [PrimeRayGram](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/PrimeRayGram.lean) | Check | `TheJointKernelOfThePrimeRaySums` |
| [SignedArithmeticCorrespondences](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences.lean) | [SquarefreeReadingsOfTheContactSpectrum](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/SquarefreeReadingsOfTheContactSpectrum.lean) · [TheSlopesOfTheCubicContactTrace](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/TheSlopesOfTheCubicContactTrace.lean) · [ValuationsFromTheCubicPrefixIncrement](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/ValuationsFromTheCubicPrefixIncrement.lean) | Check | `CountingTheTrianglesOfThePrimeContactMatrix` |
| [ZeroConfigurationGeometry](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry.lean) | [XiSlit](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/EffectiveHeights/XiSlit.lean) | Check | — |

### Additional prerequisite artifacts

These 14 imported modules need an `.olean` for the drafts above.

| Modules to build | Umbrella import | Missing imports to build first |
| --- | --- | --- |
| [PrimePowerReturnsForceSignedCancellation](../../../formal/GaloisForLFunctions/BlackHoleRingdown/TailEnergy/PrimePowerReturnsForceSignedCancellation.lean) | Already wired | — |
| [TheFoldedReadoutOfAMoebiusWindow](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/TheFoldedReadoutOfAMoebiusWindow.lean) · [TheHalfIntegerLimitsOfTheFirstSquarefreeBandwidth](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/TheHalfIntegerLimitsOfTheFirstSquarefreeBandwidth.lean) · [TheSharpHolderExponentForInfiniteGramRecovery](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/TheSharpHolderExponentForInfiniteGramRecovery.lean) | Already wired | — |
| [TheFirstMomentSeenByTheIntegratedConductorSpline](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheFirstMomentSeenByTheIntegratedConductorSpline.lean) · [TheOddFourierModesOfTheSharpPrimeMidpoint](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheOddFourierModesOfTheSharpPrimeMidpoint.lean) | Already wired | — |
| [TheMellinHeatMomentsOfTheOrdinateTail](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/TheMellinHeatMomentsOfTheOrdinateTail.lean) · [OppositeExcursionsOfTheThirdConfinedPrimeWave](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/OppositeExcursionsOfTheThirdConfinedPrimeWave.lean) | Already wired | — |
| [TheEquilibriumOfTheThreeSitePrimeGram](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/TheEquilibriumOfTheThreeSitePrimeGram.lean) | Already wired | — |
| [TheUnitCrossingsOfThreePrimePhases](../../../formal/GaloisForLFunctions/PrimeTorusTheory/Resonators/TheUnitCrossingsOfThreePrimePhases.lean) | Already wired | — |
| [TheIsolatedSitesOfThePrimeContactMatrix](../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/TheIsolatedSitesOfThePrimeContactMatrix.lean) | Already wired | — |
| [TheFullParabolicRayJetOfTheHeatFamily](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/Analysis/TheFullParabolicRayJetOfTheHeatFamily.lean) | Wire after build | — |
| [BothSignsInOneGammaAverageOfTheThirdPrimeWave](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/BothSignsInOneGammaAverageOfTheThirdPrimeWave.lean) | Wire after build | `OppositeExcursionsOfTheThirdConfinedPrimeWave` |
| [TheCommonDriftOfAllSheetsAtAHeatCollision](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/Analysis/TheCommonDriftOfAllSheetsAtAHeatCollision.lean) | Wire after build | `TheFullParabolicRayJetOfTheHeatFamily` |

## Remaining prime-probe, equilibrium, midpoint, Jensen and Xi-tilt modules

19 started modules remain. **Build** produces the `.olean` required by a dependent proof. **Check** runs Lean on the individual source. **Wire** adds the chapter umbrella import.

| Module | Remaining work | Build first |
| --- | --- | --- |
| [TheMeanSquareCorrelationOfNegativePrimeProbes](../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheMeanSquareCorrelationOfNegativePrimeProbes.lean) | Check and wire. Compiler interrupted before a result. | — |
| [TheTwoTermsOfTheEquilibriumExcess](../../../formal/GaloisForLFunctions/HTGeometry/ChronologicalTensor/Recovery/TheTwoTermsOfTheEquilibriumExcess.lean) | Check the fixes to `recovery_moment_cost` and `real_effective_potential`, then wire. | — |
| [TheNegativeRankFiveMidpoint](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheNegativeRankFiveMidpoint.lean) | Build and wire | — |
| [RealizingTheUnitaryMidpointChambers](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/RealizingTheUnitaryMidpointChambers.lean) | Build and wire | — |
| [EveryValueOfTheFivePrimeMidpoint](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/EveryValueOfTheFivePrimeMidpoint.lean) | Check and wire | [TheNegativeRankFiveMidpoint](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheNegativeRankFiveMidpoint.lean), [RealizingTheUnitaryMidpointChambers](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/RealizingTheUnitaryMidpointChambers.lean) |
| [EveryValueOfTheOddUnitaryMidpoint](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/EveryValueOfTheOddUnitaryMidpoint.lean) | Check and wire | [RealizingTheUnitaryMidpointChambers](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/RealizingTheUnitaryMidpointChambers.lean) |
| [CofinalEulerJensenTest](../../../formal/GaloisForLFunctions/FiniteFreeProbability/CofinalEulerJensenTest.lean) | Build and wire | [XiStrictRoots](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/Jensen/XiStrictRoots.lean) |
| [QuadraticCostOfEulerFilters](../../../formal/GaloisForLFunctions/FiniteFreeProbability/QuadraticCostOfEulerFilters.lean) | Build and wire | — |
| [CofinalEulerWords](../../../formal/GaloisForLFunctions/FiniteFreeProbability/CofinalEulerWords.lean) | Check and wire | [CofinalEulerJensenTest](../../../formal/GaloisForLFunctions/FiniteFreeProbability/CofinalEulerJensenTest.lean), [QuadraticCostOfEulerFilters](../../../formal/GaloisForLFunctions/FiniteFreeProbability/QuadraticCostOfEulerFilters.lean) |
| [PositiveResidueRootGeometry](../../../formal/GaloisForLFunctions/FiniteFreeProbability/PositiveResidueRootGeometry.lean) | Build and wire | — |
| [RealWeightEulerGeometry](../../../formal/GaloisForLFunctions/FiniteFreeProbability/RealWeightEulerGeometry.lean) | Build and wire | [PositiveResidueRootGeometry](../../../formal/GaloisForLFunctions/FiniteFreeProbability/PositiveResidueRootGeometry.lean) |
| [RealWeightEulerCounts](../../../formal/GaloisForLFunctions/FiniteFreeProbability/RealWeightEulerCounts.lean) | Check and wire | [RealWeightEulerGeometry](../../../formal/GaloisForLFunctions/FiniteFreeProbability/RealWeightEulerGeometry.lean) |
| [JensenSectorOfASymmetricQuartet](../../../formal/GaloisForLFunctions/FiniteFreeProbability/JensenSectorOfASymmetricQuartet.lean) | Build and wire | — |
| [WeightedJensenRoots](../../../formal/GaloisForLFunctions/VerifiedHeightRungs/WeightedJensenRoots.lean) | Build `.olean` only. Already wired. | — |
| [TheQuartetJensenRung](../../../formal/GaloisForLFunctions/VerifiedHeightRungs/TheQuartetJensenRung.lean) | Check and wire | [JensenSectorOfASymmetricQuartet](../../../formal/GaloisForLFunctions/FiniteFreeProbability/JensenSectorOfASymmetricQuartet.lean), [WeightedJensenRoots](../../../formal/GaloisForLFunctions/VerifiedHeightRungs/WeightedJensenRoots.lean) |
| [RankOfTheThetaTuranKernel](../../../formal/GaloisForLFunctions/FiniteFreeProbability/RankOfTheThetaTuranKernel.lean) | Check and wire | — |
| [ThetaJensenSaddleRoots](../../../formal/GaloisForLFunctions/FiniteFreeProbability/ThetaJensenSaddleRoots.lean) | Check and wire | — |
| [CurvatureOfTheXiSusceptibility](../../../formal/GaloisForLFunctions/ThetaCuspSections/CurvatureOfTheXiSusceptibility.lean) | Check and wire | — |
| [DirectionOfThetaRelativeEntropy](../../../formal/GaloisForLFunctions/ThetaCuspSections/DirectionOfThetaRelativeEntropy.lean) | Check and wire | — |

Two additional dependency objects are missing. Build [XiStrictRoots](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/Jensen/XiStrictRoots.lean) for `CofinalEulerJensenTest`. [ThreeBoundaryMomentsDetectEveryHeatCollision](../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/Analysis/ThreeBoundaryMomentsDetectEveryHeatCollision.lean) already passed and is wired. Its `.olean` is needed by `CollisionOrdersFromAreasOfTheHeatBoundaryMinors`.

