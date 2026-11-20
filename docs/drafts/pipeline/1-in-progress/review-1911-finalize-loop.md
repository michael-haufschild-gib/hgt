# Review-1911 finalize loop

Goal: every open module in docs/reports/review-1911/finalize.md checked, its dependency oleans built, and wired into its umbrella.

Procedure: topological order over the listed modules plus the three unlisted dependency oleans
(`RepresentationLifting/KTheory/PermutationVirtualFreeness`, `InfiniteRankWeilTheory/TheRankBarrier`,
`arithmetic-positivity-theory/Jensen/XiStrictRoots`). A module imported by another listed module is built with
`-o/-i`; every other module is checked. A passing module is wired into its umbrella (the top-level programme file;
`HTGeometry/DispersivePDE/Applications.lean` for the dispersive PDE modules).

## Status

| Module | Status |
| --- | --- |
| `SignedArithmeticCorrespondences/TheHarmonicCostOfHolesInAWeilComb` | checked, wired |
| `SignedArithmeticCorrespondences/TheFinitePartOfAShortFlatWeilComb` | checked, wired |
| `ExceptionalLayerTheory/SquareConductors/TheNegativeRankFiveMidpoint` | olean built |
| `ExceptionalLayerTheory/SquareConductors/RealizingTheUnitaryMidpointChambers` | olean built |
| `ExceptionalLayerTheory/SquareConductors/EveryValueOfTheFivePrimeMidpoint` | olean built |
| `ExceptionalLayerTheory/SquareConductors/ParitySectorMomentsAtTheUnitaryMidpoint` | checked, wired |
| `BlackHoleRingdown/TailEnergy/PrimePowerReturnsForceSignedCancellation` | olean built |
| `BlackHoleRingdown/TailEnergy/TheMobiusReadingOfTheScatteringReturns` | checked, wired |
| `RepresentationLifting/KTheory/PermutationVirtualFreeness` | olean built |
| `RepresentationLifting/KTheory/TheTensorPowersOfAPermutationCharacter` | checked, wired |
| `ExceptionalLayerTheory/SquareConductors/AllScaleFractionalReconstructionOfThePrimePrice` | checked, wired |
| `ExceptionalLayerTheory/SquareConductors/ConsecutiveRootScalesOfTheBalancedCompositePrice` | checked, wired |
| `ExceptionalLayerTheory/SquareConductors/CountingTheWidthsOfGcdExcursions` | checked, wired |
| `ExceptionalLayerTheory/SquareConductors/TheFirstMomentSeenByTheIntegratedConductorSpline` | olean built |
| `ExceptionalLayerTheory/SquareConductors/TheVariationOfTheMovingPrimeCut` | olean built |
| `ExceptionalLayerTheory/SquareConductors/RecoveringThePrimeMidpointFromConductorCuts` | checked, wired |
| `ExceptionalLayerTheory/SquareConductors/TheThreeFiniteLimitsOfAnOrdinaryPrimeMidpointStep` | checked, wired |
| `ExceptionalLayerTheory/SquareConductors/TheZeroAbscissaSeenOnLongPrimePlateaus` | checked, wired |
| `InfiniteRankWeilTheory/TheRankBarrier` | olean built |
| `GaloisTheoryOfZeros/Analysis/TheCyclicSpectrumOfTheCollisionMoments` | checked, wired |
| `ExceptionalLayerTheory/LevelWidthsOfAReflectedHadamardPair` | olean built |
| `ExceptionalLayerTheory/TheLogarithmicCorrectionToGaussianObservation` | olean built |
| `ExclusionOfTheCriticalState/Wall/OppositeExcursionsOfTheThirdConfinedPrimeWave` | olean built |
| `GaloisTheoryOfZeros/Analysis/HermiteConstantsOfTheHeatMinors` | checked |
| `GaloisTheoryOfZeros/Analysis/MultiplicityStrataOfTheHeatWinding` | olean built |
| `GaloisTheoryOfZeros/Analysis/RecoveringHeatTimeFromOneReflectedPair` | olean built |
| `GaloisTheoryOfZeros/Analysis/ThreeBoundaryMomentsDetectEveryHeatCollision` | olean built |
| `ArithmeticContinuationAndCriticalEnergy/TheHalfEndpointChargeOfADilatedLattice` | olean built |
| `ArithmeticCountingPositivity/TwoSquarefreeTranslatesInShortIntervals` | checked, wired |
| `ArithmeticPositiveDuality/TheRangeOfGreedyPrimeDeletions` | checked, wired |
| `BlackHoleRingdown/TailEnergy/CarrierFrequenciesThatMissNoResonance` | olean built |
| `BlackHoleRingdown/TailEnergy/ReadingAPulseFromItsDerivativeEnergy` | olean built |
| `BlackHoleRingdown/TailEnergy/ResonancesOfTwoSimultaneousReceiverSweeps` | olean built |
| `BlackHoleRingdown/TailEnergy/SpectraOfCascadedRectangularWindows` | olean built |
| `BlackHoleRingdown/TailEnergy/TheMomentPulsesOfAFlatWindow` | olean built |
| `BlackHoleRingdown/TailEnergy/ASingleCompactPulseDetectsEveryStrip` | olean built |
| `BlackHoleRingdown/TailEnergy/AZeroSetForTheDyadicSincPulse` | olean built |
| `BlackHoleRingdown/TailEnergy/AllMomentsOfARapidReceiverSweep` | checked, wired |
| `BlackHoleRingdown/TailEnergy/ExponentialTypeOfCascadedTimeWindows` | olean built |
| `BlackHoleRingdown/TailEnergy/AccumulatingCarriersForceTheScatteringStrip` | checked, wired |
| `BlackHoleRingdown/TailEnergy/FourExplicitPulsesDetectEveryScatteringStrip` | checked, wired |
| `BlackHoleRingdown/TailEnergy/OnePulseEnergyForcesItsOwnBlindFrequencies` | olean built |
| `BlackHoleRingdown/TailEnergy/TheExactTypeOfAWindowSpectrum` | olean built |
| `BlackHoleRingdown/TailEnergy/TheSteklovPulseSeesEveryScatteringPole` | olean built |
| `BlackHoleRingdown/TailEnergy/TheSupportEndpointsOfTheSteklovPulse` | checked, wired |
| `ConjugateDiagonalGeometry/NearLineLogMean/MertensExcursionsAtEveryLargeCutoff` | checked, wired |
| `ExceptionalLayerTheory/CountingEachMultiplicityWithoutLocatingTheZeros` | pending |
| `ExceptionalLayerTheory/CountingEveryZeroOrderByChangingTheAperture` | pending |
| `ExceptionalLayerTheory/SquareConductors/DilationsOfTheEighthPowerGcdDeficit` | pending |
| `ExceptionalLayerTheory/FiniteDerivativeSchedulesAdmitDisjointMultiplicityHistograms` | pending |
| `ExceptionalLayerTheory/SquareConductors/FirstPassageOfTheEighthPowerGcdShortfall` | pending |
| `ExceptionalLayerTheory/SquareConductors/HarmonicPhasesOfTheEighthPowerShortfall` | pending |
| `ExceptionalLayerTheory/OneLogarithmicDerivativeOrderReadsTheXiHistogram` | pending |
| `ExceptionalLayerTheory/SquareConductors/PowerDiscountsOfTheGcdShortfall` | pending |
| `ExceptionalLayerTheory/RecoveringAPoleByBarycentricInterpolation` | pending |
| `ExceptionalLayerTheory/SquareConductors/TheCountWithSmallProductOfSimplePrimeFactors` | pending |
| `ExceptionalLayerTheory/SquareConductors/TheCountingExponentOfDeletedPrimePowers` | pending |
| `ExceptionalLayerTheory/SquareConductors/TheDirichletPoleOfTheEighthPowerShortfall` | pending |
| `ExceptionalLayerTheory/SquareConductors/TheDistributionOfAccumulatedGcdShortfall` | pending |
| `ExceptionalLayerTheory/TheExactBadHeightsOfHorizontalHadamardTests` | pending |
| `ExceptionalLayerTheory/SquareConductors/TheFiniteHorizonProfileOfProperPrimePowers` | pending |
| `ExceptionalLayerTheory/SquareConductors/TheFourthOrderEvenHorizonShortfall` | pending |
| `ExceptionalLayerTheory/TheHeightErrorOfTheHadamardThreshold` | pending |
| `ExceptionalLayerTheory/TheOptimalSpacingOfFourHadamardReadings` | pending |
| `ExceptionalLayerTheory/ThePolynomialWeightsOfTheXiDivisor` | pending |
| `ExceptionalLayerTheory/TwoSpacingsOfTheExceptionalPrimeFilter` | pending |
| `ExceptionalLayerTheory/WhatTheThirdDerivativeAreaSees` | pending |
| `ExceptionalLayerTheory/SquareConductors/AlternatingCornersOfTheProperPowerHorizon` | pending |
| `ExceptionalLayerTheory/AnExplicitPrecisionForOneDerivativeArea` | pending |
| `ExceptionalLayerTheory/InferringAReflectedPairFromTwoLevelEdges` | pending |
| `ExceptionalLayerTheory/ReadingXiMultiplicityFromArbitraryNearbySites` | pending |
| `ExceptionalLayerTheory/SeparationOfTwoGaussianModesAtHighObservationHeight` | pending |
| `ExceptionalLayerTheory/TheComplexPowerSumsOfTheXiDivisorFromFourAreas` | pending |
| `ExceptionalLayerTheory/TheMeasureOfNegativeHadamardReadings` | pending |
| `Hurwitz/RealOrdersOfPerturbedPowerTails` | pending |
| `ExceptionalLayerTheory/SquareConductors/ThePowerMomentsOfEighthGridDiscrepancy` | pending |
| `ExceptionalLayerTheory/SquareConductors/TheSimplePrimeFactorsRequiredAtTheCompositeMidpoint` | pending |
| `ExceptionalLayerTheory/WhichMultiplicitiesOnePrimeRadicalAreaIdentifies` | pending |
| `ExceptionalLayerTheory/FourHorizontalSitesDetermineTheXiMultiplicity` | pending |
| `ExceptionalLayerTheory/NoncancellationOfAGaussianZeroQuartet` | pending |
| `ExceptionalLayerTheory/SquareConductors/TheConstantTermOfTheProperPowerHorizon` | pending |
| `ExclusionOfTheCriticalState/Wall/CountingSimultaneousPrimeExcursionsAtOneLevel` | pending |
| `ExclusionOfTheCriticalState/Index/MovingOrdinateBandsOfAFiniteLayer` | pending |
| `ExclusionOfTheCriticalState/Wall/BothSignsInOneGammaAverageOfTheThirdPrimeWave` | pending |
| `FamilyContinuationTheory/ChordBoundsForMellinReadingsOnTheSecondLine` | pending |
| `FamilyContinuationTheory/TheCubicProbeOnAThreeHalvesPowerMesh` | pending |
| `GaloisTheoryOfZeros/Analysis/DilationRatiosOfTheHeatBoundaryDiscriminant` | pending |
| `GaloisTheoryOfZeros/Analysis/TheFullParabolicRayJetOfTheHeatFamily` | pending |
| `GaloisTheoryOfZeros/Analysis/ExactlyWhichHeatPairsHaveAMidpointReadFromTheirGap` | pending |
| `GaloisTheoryOfZeros/Analysis/TheAreaExcessOfSimultaneousHeatCollisions` | pending |
| `GaloisTheoryOfZeros/Analysis/TheCommonDriftOfAllSheetsAtAHeatCollision` | pending |
| `GaloisTheoryOfZeros/Analysis/CollisionOrdersFromAreasOfTheHeatBoundaryMinors` | pending |
| `GaloisTheoryOfZeros/Analysis/TheMidpointResponseOfAnUnorderedHeatPair` | pending |
| `SignedArithmeticCorrespondences/TheParityMinorsOfTheCompleteWeilComb` | pending |
| `ArithmeticAuxiliaryDynamics/Spectrum/DivisorJumpStability` | pending |
| `BezoutValuationIncidence/Sieve/GramOfThePrimeSquarefreeDifferences` | pending |
| `BezoutValuationIncidence/Sieve/TheCostOfDeletingPrimesFromSquarefreeCounts` | pending |
| `BlackHoleRingdown/TailEnergy/SectorEnergyMultiplier` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/ACubeRootGapForConsecutiveSquarefreePairs` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/PhaseRetrievalFromWideWindowSlopes` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/TheRegularPartOfSquarefreeSections` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/TheSharpHolderExponentForInfiniteGramRecovery` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/TheEndpointFormOfTheMoebiusMean` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/TheMicroscopicCovarianceOfSharpMoebiusSections` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/ShortSectionsInsideLongCriticalMeans` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/DriftingCriticalPrefixes` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/DyadicPhaseSelection` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/SuperpolynomialMobiusOrder` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/ThePackingOrderOfOneSignMertensIntervals` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/AdmissibleLongMomentExponents` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/AnchoredBandwidth` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/JetsOfDyadicSquarefreeSections` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/OptimalHarmonicRecoveryOfTheSquarefreeLaurentGerm` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/OptimalReadingsForOneMoreCoefficient` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/OrthogonalHeightsOfTheSharpMoebiusSections` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/TheFoldedReadoutOfAMoebiusWindow` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/FourFoldedReadings` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/SquarefreeDyadicCovariance` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/TheHalfIntegerLimitsOfTheFirstSquarefreeBandwidth` | pending |
| `ConjugateDiagonalGeometry/NearLineLogMean/TheAgeExpansionOfTheFirstSquarefreeBandwidth` | pending |
| `ExceptionalLayerTheory/SquareConductors/TheOddFourierModesOfTheSharpPrimeMidpoint` | pending |
| `ExceptionalLayerTheory/SquareConductors/RecoveringPrimePairsFromTranslatedMidpoints` | pending |
| `ExceptionalLayerTheory/DampingMinimum` | pending |
| `ExceptionalLayerTheory/SquareConductors/ConductorSensitivity` | pending |
| `ExceptionalLayerTheory/SquareConductors/MidpointPrimePairVariation` | pending |
| `ExclusionOfTheCriticalState/Index/CriticalHeatProfile` | pending |
| `ExclusionOfTheCriticalState/Index/GeometricWallShells` | pending |
| `ExclusionOfTheCriticalState/Wall/PrimeRectangles` | pending |
| `ExclusionOfTheCriticalState/Index/TheMellinHeatMomentsOfTheOrdinateTail` | pending |
| `ExclusionOfTheCriticalState/Index/CoalescingHeatRates` | pending |
| `ExclusionOfTheCriticalState/Wall/ConfinedLaplaceSaddle` | pending |
| `FamilyContinuationTheory/CubicDyadicSampling` | pending |
| `FiniteFreeProbability/Composition/JensenDegreeExpansion` | pending |
| `GaloisTheoryOfZeros/Analysis/TheCubicDisplacementOfTheHeatSheets` | pending |
| `MultiplicativePositivityGeometry/TheEquilibriumOfTheThreeSitePrimeGram` | pending |
| `MultiplicativePositivityGeometry/CollapsedPrimeSites` | pending |
| `MultiplicativePositivityGeometry/SpreadingPrimeGramMassOnTwoLogarithmicSteps` | pending |
| `MultiplicativePositivityGeometry/ThreeSiteCrossover` | pending |
| `PrimeTorusTheory/Resonators/TheUnitCrossingsOfThreePrimePhases` | pending |
| `PrimeTorusTheory/Resonators/SignedTraces` | pending |
| `RestrictedFactorizationCalculus/TheSmoothDensityReadByTheRelativeSignRadius` | pending |
| `RestrictedFactorizationCalculus/UniformlyTiltingTheEulerPriceAtOne` | pending |
| `RestrictedFactorizationCalculus/TheUniformErasureThresholdOfPolynomialPrimeBands` | pending |
| `SignedArithmeticCorrespondences/TheJointKernelOfThePrimeRaySums` | pending |
| `SignedArithmeticCorrespondences/TheIsolatedSitesOfThePrimeContactMatrix` | pending |
| `SignedArithmeticCorrespondences/TheFirstOddMomentOfThePrimeContactMatrix` | pending |
| `SignedArithmeticCorrespondences/CountingTheTrianglesOfThePrimeContactMatrix` | pending |
| `SignedArithmeticCorrespondences/PrimeContactPathsBeforeTheFirstSquare` | pending |
| `SignedArithmeticCorrespondences/PrimeCutSpectrum` | pending |
| `SignedArithmeticCorrespondences/TheKernelFiltrationOfDirectedPrimeContacts` | pending |
| `SignedArithmeticCorrespondences/PrimeRayGram` | pending |
| `SignedArithmeticCorrespondences/SquarefreeReadingsOfTheContactSpectrum` | pending |
| `SignedArithmeticCorrespondences/TheSlopesOfTheCubicContactTrace` | pending |
| `SignedArithmeticCorrespondences/ValuationsFromTheCubicPrefixIncrement` | pending |
| `ZeroConfigurationGeometry/EffectiveHeights/XiSlit` | pending |
| `CountingHolography/Sections/TheMeanSquareCorrelationOfNegativePrimeProbes` | pending |
| `HTGeometry/ChronologicalTensor/Recovery/TheTwoTermsOfTheEquilibriumExcess` | pending |
| `ExceptionalLayerTheory/SquareConductors/EveryValueOfTheOddUnitaryMidpoint` | pending |
| `arithmetic-positivity-theory/Jensen/XiStrictRoots` | pending |
| `FiniteFreeProbability/CofinalEulerJensenTest` | pending |
| `arithmetic-positivity-theory/Jensen/XiStrictRoots` | pending |
| `FiniteFreeProbability/QuadraticCostOfEulerFilters` | pending |
| `FiniteFreeProbability/CofinalEulerWords` | pending |
| `FiniteFreeProbability/PositiveResidueRootGeometry` | pending |
| `FiniteFreeProbability/RealWeightEulerGeometry` | pending |
| `FiniteFreeProbability/RealWeightEulerCounts` | pending |
| `FiniteFreeProbability/JensenSectorOfASymmetricQuartet` | pending |
| `VerifiedHeightRungs/WeightedJensenRoots` | pending |
| `VerifiedHeightRungs/TheQuartetJensenRung` | pending |
| `FiniteFreeProbability/RankOfTheThetaTuranKernel` | pending |
| `FiniteFreeProbability/ThetaJensenSaddleRoots` | pending |
| `ThetaCuspSections/CurvatureOfTheXiSusceptibility` | pending |
| `ThetaCuspSections/DirectionOfThetaRelativeEntropy` | pending |
| `ExceptionalLayerTheory/SquareConductors/ThinningThePowerSamplesOfTheReciprocalPrimeOctave` | pending |
| `ExceptionalLayerTheory/SquareConductors/TheFactorialCenterOfTheSmallUnitaryDivisors` | pending |
| `ExclusionOfTheCriticalState/Wall/ReciprocalWeightDistortionOnJointPrimeExcursions` | pending |
| `ExclusionOfTheCriticalState/Wall/OneSuperlevelOfTheOppositePrimeMoment` | pending |
| `ExclusionOfTheCriticalState/Wall/TheFlankContrastInTheOppositePrimeMoment` | pending |
| `ExclusionOfTheCriticalState/Wall/UniformCancellationOnTruncatedOddQuotientIntervals` | pending |
| `ExclusionOfTheCriticalState/Wall/ThePowerSavingOnEveryOddQuotientDenominatorInterval` | pending |
| `ExclusionOfTheCriticalState/Wall/TheDiagonalCutoffForSquareRootNormalizedPrimeExcursions` | pending |
| `HTGeometry/DispersivePDE/TheGrossPitaevskiiCorrectorOfTheKdVPulse` | pending |
| `HTGeometry/DispersivePDE/TheDensityShearOfAGreyGrossPitaevskiiSoliton` | pending |
| `CompactHyperbolicSurfaces/LogarithmicDistortionOfAutomorphicKernels` | pending |
| `ArithmeticAuxiliaryDynamics/Spectrum/TheHardyEnergyOfFloorExcessTails` | pending |
| `GaloisTheoryOfZeros/Analysis/TwoFocusBoundsForTheUnshiftedJensenPolynomials` | pending |
| `GaloisTheoryOfZeros/Analysis/TheGeometricMeanOfAHeatBoundaryDiscriminant` | pending |
| `GaloisTheoryOfZeros/OneRationalHeightComparisonPerJensenDegree` | pending |
| `GaloisTheoryOfZeros/ErrorsAndDensitiesInTheScheduledJensenTest` | pending |
| `BlackHoleRingdown/TailEnergy/QuadraticPhaseRecoveryOfTheCompleteReceiverMatrix` | pending |
