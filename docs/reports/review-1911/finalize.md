## §2.11 Quantitative factorization with signed boundaries

The remaining drafts below need a successful Lean check and an import in [RestrictedFactorizationCalculus.lean](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus.lean). All five modules for stopping depth and critical smooth counts now compile and are wired, through [TheSecondCoefficientAtTheLogSquareWall](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheSecondCoefficientAtTheLogSquareWall.lean).

| Paper argument | Pending modules, with prerequisites first |
| --- | --- |
| Moving cutoffs and signed rough prefixes | [PrimeArrivalsAtAMovingLogSquareWall](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/PrimeArrivalsAtAMovingLogSquareWall.lean) |
| Least-prime rows and semiprime windows | [TheExactFlowAcrossLeastPrimeBranches](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheExactFlowAcrossLeastPrimeBranches.lean) |
| Restricted exchanges and fixed vertices | [BoundedStretchForPerfectRestrictedMatchings](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/BoundedStretchForPerfectRestrictedMatchings.lean) · [TheSignedPrefixOfOneTruncatedExchange](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheSignedPrefixOfOneTruncatedExchange.lean) · [PrescribingExchangesOnADensityZeroSet](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/PrescribingExchangesOnADensityZeroSet.lean) · [OneDensityZeroFamilyDetectingTheMertensExponent](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/OneDensityZeroFamilyDetectingTheMertensExponent.lean) · [SimultaneousPowerDetectionByFixedAndCrossingVertices](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/SimultaneousPowerDetectionByFixedAndCrossingVertices.lean) · [LogarithmicMomentsOfTheFixedDivisors](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/LogarithmicMomentsOfTheFixedDivisors.lean) · [OptimalityOfAlternatingTransport](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/OptimalityOfAlternatingTransport.lean) |
| Displacement and prescribed smaller primes | [UniformSurvivorsOfSparseDivisors](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/UniformSurvivorsOfSparseDivisors.lean) · [IsolatedIntegersForBoundedExchangeTables](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/IsolatedIntegersForBoundedExchangeTables.lean) · [BothSignsOnEverySmoothOctave](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/BothSignsOnEverySmoothOctave.lean) · [LongExchangesOnEverySmoothOctave](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/LongExchangesOnEverySmoothOctave.lean) · [TheParityCostOfRestrictingTheSmallerPrime](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheParityCostOfRestrictingTheSmallerPrime.lean) · [PrimeDonorsWithAPrescribedSmallerPrime](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/PrimeDonorsWithAPrescribedSmallerPrime.lean) · [DonorsFromDisjointPairsOfPrimes](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/DonorsFromDisjointPairsOfPrimes.lean) |

**Dependency builds.** [TotalVariationOfTheRemovedQuotientHead](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TotalVariationOfTheRemovedQuotientHead.lean) compiled and is wired. Its olean is available to `PrimeArrivalsAtAMovingLogSquareWall`, which also needs the public `rough_coefficient_le_log` from [RoughDivisorInversionAtTheHyperbola](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/RoughDivisorInversionAtTheHyperbola.lean). The exchange modules need `dense_prime_range_table_at_every_prefix` from [DensityOneForRestrictedPrimeExchanges](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/DensityOneForRestrictedPrimeExchanges.lean) and `coprime_without_gcd` from [ReversibleSwitchesOnPrimeRanges](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/ReversibleSwitchesOnPrimeRanges.lean) in their compiled interfaces.

**Scope.** The two donor modules cover the paper arguments for donor supply and reversible switches. Attainment by the full prescribed-smaller-prime matching remains conjectural. The whole-window semiprime flux, the proposed natural-wall variation constant, and the square-root bound on the recombined interior also remain open.

**Other modules in the shared directory.** [OneCofactorAtEveryDyadicQuotient](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/OneCofactorAtEveryDyadicQuotient.lean) · [TheStripSeenThroughAnArbitrarilyShortCofactorRange](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheStripSeenThroughAnArbitrarilyShortCofactorRange.lean). The strip module is wired. The dyadic quotient module still needs its umbrella import. Successful source checks for both remain unconfirmed.


## Cubic fields, scattering and quantum heating

112 of 117 started modules compiled and are wired. These 5 drafts still need a confirmed successful Lean check and an import in the indicated umbrella.

| Area | Pending modules | Umbrella |
| --- | --- | --- |
| Cubic mode recovery | [CoupledCubicVelocityInverse](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Modes/CoupledCubicVelocityInverse.lean) · [CubicProbeMinimax](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Modes/CubicProbeMinimax.lean) | [ExclusionOfTheCriticalState](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState.lean) |
| Dispersive scattering | [CubicGraphScattering](../../../formal/GaloisForLFunctions/HTGeometry/DispersivePDE/CubicGraphScattering.lean) · [CubicScatteringSpectrum](../../../formal/GaloisForLFunctions/HTGeometry/DispersivePDE/CubicScatteringSpectrum.lean) | [Applications](../../../formal/GaloisForLFunctions/HTGeometry/DispersivePDE/Applications.lean) |
| Velocity recovery | [SparseVelocityInverse](../../../formal/GaloisForLFunctions/HTGeometry/KleinGordon/SparseVelocityInverse.lean) | [HTGeometry](../../../formal/GaloisForLFunctions/HTGeometry.lean) |

All six quantum-heating modules compile and are wired, through the sharp one- and two-channel sampling thresholds in [SchwartzHeatingSampling](../../../formal/GaloisForLFunctions/HTGeometry/QuantumChannels/SchwartzHeatingSampling.lean).

## §2.18 Prime midpoint formalization

All nine listed modules compile and are wired. The cubic triple-price difference equals the difference of the two sharp prime boxes. Both power-grid floor costs have logarithmic coefficient one half. The fourth-root cutoff gives an error of order $n^{1/2+ε}$ for every $ε>0$. The Mellin transform of the signed midpoint weight under a common random dilation equals the stated dyadic multiplier. [Triple boxes](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeCountsInTheTwoMidpointTripleBoxes.lean) · [Floor costs](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheAccumulatedFloorOnPowerSampledPrimeOctaves.lean) · [Fourth-root estimate](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheSmoothFactorAtTheFourthRootMidpoint.lean) · [Mellin identity](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheMellinMultiplierOfTheSmoothPrimeMidpoint.lean)

## §2.11 Outstanding dependency builds

| Module | Remaining work |
| --- | --- |
| `RoughDivisorInversionAtTheHyperbola` | Source defines `rough_coefficient_le_log`. The compiled interface lacks it, blocking `PrimeArrivalsAtAMovingLogSquareWall`. |
| `DensityOneForRestrictedPrimeExchanges` | Source defines `dense_prime_range_table_at_every_prefix`. The compiled interface lacks it, blocking `BoundedStretchForPerfectRestrictedMatchings`. |
| `ReversibleSwitchesOnPrimeRanges` | Source exports `coprime_without_gcd`. The compiled interface has only its private name, blocking `SimultaneousPowerDetectionByFixedAndCrossingVertices`. |
