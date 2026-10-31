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

Umbrella for indefinite harmonic analysis on the dilation–translation system of `ℚ`: the index of
induced states, witness complements and escape, the affine zero-or-infinity law and the Kakutani
wall as an index wall, the Pontryagin extensions of Weil's correlation, mixing and height decay,
the signature formula of separable assemblies, conformal symmetry and its negative square,
stable conformal successors and their function-field calibration, the pole as a Krein state of the
affine group, the affine group of a field, conformal induction and the pole–successor states at every place
of `ℚ` and at infinity of `F(X)`, with the signature formula `κ = κ₀(ψ) + 1` the shell decomposition of the local forms, Weil's correlation with an archimedean successor,
twin-blindness of the index, the adelic product state, the running counterterm of the prime
kernel, archimedean continuity against height decay, the additive and Ramanujan index laws on `ℤ/N` and `ℚ/ℤ`, and a Haar
successor with one negative square. Positive integer-successor carriers
preserve slope index; continuous dilations force infinite index for every such carrier with
a slope correction. A mixed quadratic perturbation preserves both Haar axis readings while
adding exactly three negative squares and unbounded mixed coefficients.
A nonzero affine kernel vanishing on both axes has at least two negative squares.
Every such kernel with finite index `r` has column-space dimension at most `r²`.
See `AdelicKreinGeometry/README.md`.
-/
