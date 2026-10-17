import GaloisForLFunctions.BiScaleUncertainty.KreinIncrementAndChordCascade
import GaloisForLFunctions.BiScaleUncertainty.MultiplicativeChainBesselAndOriginLeverage
import GaloisForLFunctions.BiScaleUncertainty.OptimalOriginAllocation
import GaloisForLFunctions.BiScaleUncertainty.OverlapSafeCollarMeasureTransport
import GaloisForLFunctions.BiScaleUncertainty.LogarithmicCollarCoverage
import GaloisForLFunctions.BiScaleUncertainty.SignedDyadicCollarPartition
import GaloisForLFunctions.BiScaleUncertainty.IntegratedOriginCollarLeverage
import GaloisForLFunctions.BiScaleUncertainty.MultiChainToeplitzGramCoupling
import GaloisForLFunctions.BiScaleUncertainty.TriangularGramSineBound
import GaloisForLFunctions.BiScaleUncertainty.SynchronizedCosetSineLeverage
import GaloisForLFunctions.BiScaleUncertainty.HyperbolicPolarBalanceAndLevySinhFunctional
import GaloisForLFunctions.BiScaleUncertainty.FoldedCollarIntegralAndObstructionResolution
import GaloisForLFunctions.BiScaleUncertainty.SharedOriginMultiCosetLeverage
import GaloisForLFunctions.BiScaleUncertainty.DistantCopyPolarEnforcement

/-!
# Bi-Scale / Logarithmic-Grid Uncertainty Theory (`GaloisForLFunctions.BiScaleUncertainty`)

Umbrella module for **Bi-Scale / Logarithmic-Grid Uncertainty Theory**, an independent mathematical
field studying the non-local geometry, multi-node Bessel/Gram rigidity, and singular increment
functionals of positive-definite translation correlation kernels `h = f ⋆ f̃` under simultaneous
discrete logarithmic-grid pinning and hyperbolic polar moment constraints.

See `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` for the motivation, structural
diagnosis, and four-pillar architecture of the field.

## Foundational Modules

1. `GaloisForLFunctions.BiScaleUncertainty.KreinIncrementAndChordCascade`:
   Translation chord distance `d_f(x, y) = √(2 (h(0) - h(x - y)))`, Peter–Paul chord inequality,
   subadditive chord triangle law, quadratic multiple & dyadic cascade bounds, derivative-free
   harmonic/dyadic sub-grid lower bounds at zero nodes, and Krein's positive-definite increment
   inequality.
2. `GaloisForLFunctions.BiScaleUncertainty.MultiplicativeChainBesselAndOriginLeverage`:
   Multi-node orthogonal-frame Bessel inequality, origin-anchored left/right-collar Euclidean
   Sphere Laws, the Origin-Singularity Leverage Theorem, and logarithmic divisibility / dyadic-coset
   chains on `Λ_N = {log n : 2 ≤ n ≤ N}`.
3. `GaloisForLFunctions.BiScaleUncertainty.HyperbolicPolarBalanceAndLevySinhFunctional`:
   Exact pole-eliminated Weil–Lévy identity on the hyperbolic polar hyperplane, positive/negative
   lobe decomposition and hyperbolic lobe conservation, and the Polar–Lévy kernel deformation and
   crossover floor.
4. `GaloisForLFunctions.BiScaleUncertainty.FoldedCollarIntegralAndObstructionResolution`:
   Resolves the single-point non-dyadic interpolation obstruction (`4 log 2 / 5`) by folding `[a, t₁ - a]`
   around `t₁ / 2` and proving an unconditional, strictly positive lower bound on the Bi-Scale Lévy
   energy `biScaleLevyEnergy f` and on `weilArchRe` for smooth EWU tests (`RealSmoothEvenPolarTestFn`).
5. `GaloisForLFunctions.BiScaleUncertainty.SharedOriginMultiCosetLeverage`:
   Exact shared-origin block support bound and equality witness, rationalized cross-coset cost,
   and simultaneous dyadic-coset leverage without counting the origin energy repeatedly.
6. `GaloisForLFunctions.BiScaleUncertainty.DistantCopyPolarEnforcement`:
   A concrete polar source preserving normalized correlations on any bounded interval, with
   explicit exponentially small energy error; equality of all polar and nonpolar grid lower bounds.
7. `GaloisForLFunctions.BiScaleUncertainty.IntegratedOriginCollarLeverage`:
   Exact finite-interval collar transport with measurable optimal signed-coset origin shares
   and a strictly positive finite real coefficient for compact-continuous grid sources.
-/
