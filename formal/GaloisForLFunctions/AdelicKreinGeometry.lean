import GaloisForLFunctions.AdelicKreinGeometry.Haar.ScaledHaarObstruction
import GaloisForLFunctions.AdelicKreinGeometry.Haar.FiniteIndexObstruction
import GaloisForLFunctions.AdelicKreinGeometry.Haar.CyclicGramLimit
import GaloisForLFunctions.AdelicKreinGeometry.Haar.CyclicHecke
import GaloisForLFunctions.AdelicKreinGeometry.Haar.CyclicOrbits
import GaloisForLFunctions.AdelicKreinGeometry.Haar.TranslationMovingPositivity
import GaloisForLFunctions.AdelicKreinGeometry.Haar.PolynomialCorrection
import GaloisForLFunctions.AdelicKreinGeometry.Haar.PeriodDefects
import GaloisForLFunctions.AdelicKreinGeometry.TheIndexOfAnInducedState
import GaloisForLFunctions.AdelicKreinGeometry.TheWitnessComplementIsPositive
import GaloisForLFunctions.AdelicKreinGeometry.HeckeSupportedStatesHaveIndexZeroOrInfinity
import GaloisForLFunctions.AdelicKreinGeometry.ThePontryaginExtensionsOfWeilsCorrelation
import GaloisForLFunctions.AdelicKreinGeometry.MixingKillsNegativeSquares
import GaloisForLFunctions.AdelicKreinGeometry.TheSignatureOfASeparableAssembly
import GaloisForLFunctions.AdelicKreinGeometry.ConformalSymmetryNeedsANegativeSquare
import GaloisForLFunctions.AdelicKreinGeometry.TheIndexIsTwinBlind
import GaloisForLFunctions.AdelicKreinGeometry.TheAdelicProductState
import GaloisForLFunctions.AdelicKreinGeometry.NoFixedCountertermMakesThePrimeKernelPontryagin
import GaloisForLFunctions.AdelicKreinGeometry.ArchimedeanContinuityAgainstHeightDecay
import GaloisForLFunctions.AdelicKreinGeometry.TheAdditiveIndexLaw
import GaloisForLFunctions.AdelicKreinGeometry.TheAdditiveIndexLawOnQModZ
import GaloisForLFunctions.AdelicKreinGeometry.TheRamanujanIndexLaw
import GaloisForLFunctions.AdelicKreinGeometry.StableConformalSuccessors
import GaloisForLFunctions.AdelicKreinGeometry.TheFunctionFieldConformalSuccessor
import GaloisForLFunctions.AdelicKreinGeometry.TheAffineGroupOfAField
import GaloisForLFunctions.AdelicKreinGeometry.ThePoleIsAKreinStateOfTheAffineGroup
import GaloisForLFunctions.AdelicKreinGeometry.TheHeckeBoostAndTheConformalSuccessorAreOneState
import GaloisForLFunctions.AdelicKreinGeometry.EveryPlaceCarriesAPoleSuccessorState
import GaloisForLFunctions.AdelicKreinGeometry.ThePoleSuccessorSignatureFormula
import GaloisForLFunctions.AdelicKreinGeometry.TheShellDecompositionOfAPoleSuccessorForm
import GaloisForLFunctions.AdelicKreinGeometry.WeilsCorrelationWithAnArchimedeanSuccessor
import GaloisForLFunctions.AdelicKreinGeometry.LocalSignaturesAddOverDistinctPlaces
import GaloisForLFunctions.AdelicKreinGeometry.TheArchimedeanGluingFormula
import GaloisForLFunctions.AdelicKreinGeometry.WeilsArchimedeanStateCountsTheZeros
import GaloisForLFunctions.AdelicKreinGeometry.TheGluingSquareIsSharp
import GaloisForLFunctions.AdelicKreinGeometry.PrimeTowersGlueAtFullIndex
import GaloisForLFunctions.AdelicKreinGeometry.Haar.OneNegativeSquare
import GaloisForLFunctions.AdelicKreinGeometry.Haar.IndexPreservation
import GaloisForLFunctions.AdelicKreinGeometry.Haar.ContinuousDilationsNeedInfiniteIndex
import GaloisForLFunctions.AdelicKreinGeometry.Haar.MixedPolynomialPerturbation
import GaloisForLFunctions.AdelicKreinGeometry.Haar.AxisInvisibility
import GaloisForLFunctions.AdelicKreinGeometry.Haar.FiniteRankPerturbations
import GaloisForLFunctions.AdelicKreinGeometry.Haar.PolynomialPerturbations
import GaloisForLFunctions.AdelicKreinGeometry.Haar.PowerKernels

/-!
# Adelic Krein Geometry

Umbrella for the index theory of Hermitian states on the dilation–translation system of `ℚ` and of
its places.

* Index calculus on groups: induced states, witness complements and escape, mixing and height decay,
  twin-blindness, block additivity.
* Arithmetic types: the affine zero-or-infinity law, the Kakutani wall as an index wall, Weil's affine
  extensions, the running counterterm of the prime kernel, archimedean continuity against height
  decay, the adelic product state.
* Additive side: the additive and Ramanujan index laws on `ℤ/N` and `ℚ/ℤ`, conditionally positive
  successors (`−|b|`, `−|b|^s`, ultrametric `−|b|_v`, `−|·|_∞` on `F[X]`).
* Conformal and pole structure: conformal symmetry costs one square; the pole as a Krein state;
  conformal induction and the pole–successor states over any field and place, their signature formula
  `κ = κ₀(ψ) + 1`, additivity over places, shell decompositions.
* Gluing at the archimedean place: the boost-polar index, the gluing formula `κ = κ^{(½)}(K) + 1`, free
  hyperplanes for sub-boost and periodic data, prime towers, and the count
  `κ = #{zeros right of the line} + 1` for Weil's archimedean state and for Dirichlet L-functions.
* Haar carriers (`Haar/`): index preservation by positive integer-successor carriers, axis-invisible
  kernels and their degree and rank laws, period defects, and infinite index for every Haar kernel
  with a continuous dilation reading.

See `AdelicKreinGeometry/README.md`.
-/
