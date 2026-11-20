## §2.11 Quantitative factorization with signed boundaries

[BoundedStretchForPerfectRestrictedMatchings](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/BoundedStretchForPerfectRestrictedMatchings.lean) is the only draft awaiting a successful Lean check and [umbrella import](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus.lean). The existing compiled interface for [DensityOneForRestrictedPrimeExchanges](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/DensityOneForRestrictedPrimeExchanges.lean) lacks `dense_prime_range_table_at_every_prefix`. The dependency source passes with that theorem.

All five modules for stopping depth and critical smooth counts compile and are wired, through [TheSecondCoefficientAtTheLogSquareWall](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheSecondCoefficientAtTheLogSquareWall.lean).

The moving-cutoff and least-prime modules compile and are wired. The head-variation bound follows from the existing square-crossing estimate at the squares of the two heights. [PrimeArrivalsAtAMovingLogSquareWall](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/PrimeArrivalsAtAMovingLogSquareWall.lean) · [TheExactFlowAcrossLeastPrimeBranches](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheExactFlowAcrossLeastPrimeBranches.lean)

**Scope.** The two donor modules cover the paper arguments for donor supply and reversible switches. Attainment by the full prescribed-smaller-prime matching remains conjectural. The whole-window semiprime flux, the proposed natural-wall variation constant, and the square-root bound on the recombined interior also remain open.

The two cofactor-range modules compile and are wired. [OneCofactorAtEveryDyadicQuotient](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/OneCofactorAtEveryDyadicQuotient.lean) · [TheStripSeenThroughAnArbitrarilyShortCofactorRange](../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheStripSeenThroughAnArbitrarilyShortCofactorRange.lean).

## Cubic fields, scattering and quantum heating

All 117 started modules compile and are wired. These include the four-shot cubic minimax bounds, sparse velocity recovery, and the real factorization of the scattering polynomial.

All six quantum-heating modules compile and are wired, through the sharp one- and two-channel sampling thresholds in [SchwartzHeatingSampling](../../../formal/GaloisForLFunctions/HTGeometry/QuantumChannels/SchwartzHeatingSampling.lean).

## §2.18 Prime midpoint formalization

All nine listed modules compile and are wired. The cubic triple-price difference equals the difference of the two sharp prime boxes. Both power-grid floor costs have logarithmic coefficient one half. The fourth-root cutoff gives an error of order $n^{1/2+ε}$ for every $ε>0$. The Mellin transform of the signed midpoint weight under a common random dilation equals the stated dyadic multiplier. [Triple boxes](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeCountsInTheTwoMidpointTripleBoxes.lean) · [Floor costs](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheAccumulatedFloorOnPowerSampledPrimeOctaves.lean) · [Fourth-root estimate](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheSmoothFactorAtTheFourthRootMidpoint.lean) · [Mellin identity](../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheMellinMultiplierOfTheSmoothPrimeMidpoint.lean)
