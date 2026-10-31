import GaloisForLFunctions.HeckeKreinToeplitz.Index.MonotoneHermitianForms
import GaloisForLFunctions.HeckeKreinToeplitz.Index.HermitianFiniteSums
import GaloisForLFunctions.HeckeKreinToeplitz.Index.PositiveCoefficients
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ConstantMatrixInertia
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnPositivity
import GaloisForLFunctions.HeckeKreinToeplitz.Index.PeriodicDilationPositivity
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnProjections
import GaloisForLFunctions.HeckeKreinToeplitz.Index.LocallyPeriodicProjection
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ProjectionFunctoriality
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ProjectionOrder
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnInertia
import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteRankPerturbations
import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteRankStability
import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteColumns
import GaloisForLFunctions.HeckeKreinToeplitz.Index.NilpotentSubspaces
import GaloisForLFunctions.HeckeKreinToeplitz.KernelsOnGroupsAndTheirNegativeIndex
import GaloisForLFunctions.HeckeKreinToeplitz.HyperbolicPairsAndTheIndexFormula
import GaloisForLFunctions.HeckeKreinToeplitz.BoundedIndexIsClosedUnderPointwiseLimits
import GaloisForLFunctions.HeckeKreinToeplitz.FiniteIndexIsPositiveMinusFiniteRank
import GaloisForLFunctions.HeckeKreinToeplitz.Index.NullKernelRigidity
import GaloisForLFunctions.HeckeKreinToeplitz.Index.NullSubgroupRank
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnRepresentation
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnForm
import GaloisForLFunctions.HeckeKreinToeplitz.Index.IsotropicSubspaces
import GaloisForLFunctions.HeckeKreinToeplitz.Index.SubgroupColumns
import GaloisForLFunctions.HeckeKreinToeplitz.Index.HyperbolicFeatures
import GaloisForLFunctions.HeckeKreinToeplitz.Index.RescalingInvariance
import GaloisForLFunctions.HeckeKreinToeplitz.TheIndexOfAFiniteExponentialSum
import GaloisForLFunctions.HeckeKreinToeplitz.TheIndexOfABohrSeries
import GaloisForLFunctions.HeckeKreinToeplitz.TheIndexUnderRotationDampingAndCoalescence
import GaloisForLFunctions.HeckeKreinToeplitz.GrowthReadsTheDepthOfTheDeepestPair
import GaloisForLFunctions.HeckeKreinToeplitz.HigherMomentsAreHigherInertia
import GaloisForLFunctions.HeckeKreinToeplitz.LogarithmicCharactersAndTheArithmeticIndexFormula
import GaloisForLFunctions.HeckeKreinToeplitz.StepanovCompressionsAndTheAnnihilationLaw
import GaloisForLFunctions.HeckeKreinToeplitz.OneGridHidesTwoGridsDecide
import GaloisForLFunctions.HeckeKreinToeplitz.AllButFinitelyManyPrimesSeeTheWholeIndex
import GaloisForLFunctions.HeckeKreinToeplitz.LocalityFailsButAlmostEveryPrimeDecides
import GaloisForLFunctions.HeckeKreinToeplitz.WeilsIndexIsCountedByTheOuterFrobeniusEigenvalues
import GaloisForLFunctions.HeckeKreinToeplitz.TheHeckeOrbitKernelOfAZeroConfiguration
import GaloisForLFunctions.HeckeKreinToeplitz.TheArchimedeanCompletionCarriesTheSameIndex
import GaloisForLFunctions.HeckeKreinToeplitz.TheFiniteIndexStratumOfZetaIsLindelofDeep
import GaloisForLFunctions.HeckeKreinToeplitz.TheWeilKernelIsKreinLangerOnTheFiniteStratum
import GaloisForLFunctions.HeckeKreinToeplitz.TheConverseKreinLangerTheoremForOrbitKernels
import GaloisForLFunctions.HeckeKreinToeplitz.HeightTruncationsCarryTheIndexToTheLimit
import GaloisForLFunctions.HeckeKreinToeplitz.IndexIsEnergy
import GaloisForLFunctions.HeckeKreinToeplitz.IntegerFamiliesCarryTheWholeIndex
import GaloisForLFunctions.HeckeKreinToeplitz.EveryReceiverAtEveryWidthIsBoundedByTheIndex
import GaloisForLFunctions.HeckeKreinToeplitz.ShrinkingAtomsCarryTheWholeIndex
import GaloisForLFunctions.HeckeKreinToeplitz.TheReceiversEndAtTheQuasiAnalyticBoundary
import GaloisForLFunctions.HeckeKreinToeplitz.HeatCollisionsCountTheIndex
import GaloisForLFunctions.HeckeKreinToeplitz.TheGlobalLawIsTheOneSidedSquareRootCount
import GaloisForLFunctions.HeckeKreinToeplitz.TheSelectivityBatteryOnPrimeTowers
import GaloisForLFunctions.HeckeKreinToeplitz.IndexZeroSelectsTheVonMangoldtWeight
import GaloisForLFunctions.HeckeKreinToeplitz.OnePrimeTowerCountsTheDistinctFrobeniusValues
import GaloisForLFunctions.HeckeKreinToeplitz.TheNyquistLawOfAPrimeTower
import GaloisForLFunctions.HeckeKreinToeplitz.TheGoldenCurveIsDecidedOnItsTowerButNotOnTheLattice
import GaloisForLFunctions.HeckeKreinToeplitz.ThePoleIsTheOnlyRemovableHyperbolicDirection
import GaloisForLFunctions.HeckeKreinToeplitz.TheMarginIsTheWidthOfTheIndexOneWindow
import GaloisForLFunctions.HeckeKreinToeplitz.TheSelectiveIndexOfTheAtomicKernelIsOneSquare
import GaloisForLFunctions.HeckeKreinToeplitz.APurePointSpectrumIsThinAtMostFrequencies
import GaloisForLFunctions.HeckeKreinToeplitz.OnTheFiniteStratumEveryFlipHasInfiniteIndex
import GaloisForLFunctions.HeckeKreinToeplitz.EveryFlipSetHasInfiniteIndexOnTheHeckeLattice

/-!
# Hecke-covariant Krein–Toeplitz theory

Hermitian kernels with finitely many negative squares on groups, and on the Hecke lattice
`ℚ_{>0}` in particular, with the Weil kernel of `ζ` as the arithmetic instance.

* **Structure.** The negative index of a kernel; hyperbolic pairs and the Krein–Langer index
  formula; the exact index of a finite exponential sum without separation and of an absolutely
  convergent Bohr series; finite index as
  positive definite minus finite rank (Pontryagin decomposition),
  attainment and subadditivity; subgroup zero sets for null kernels of index one;
  rank at most the square of the index from two zero subgroup readings;
  an algebraic column representation recovering every group kernel as a coefficient;
  closedness under pointwise limits; growth and self-upgrade; higher
  moments as higher inertia; rotation, damping and coalescence.
* **Arithmetic characters.** Logarithmic characters and the arithmetic index formula; Stepanov
  compressions and the annihilation law.
* **Local-to-global.** The aliasing law on one prime, the Nyquist law at bounded height, the
  two-prime law, finitely many blind primes; the failure of locality on `ℤ²` and its arithmetic
  repair.
* **Calibration over `𝔽_q`.** The index of a curve trace kernel counts the outer Frobenius
  eigenvalues; index zero is the square-root count; the golden curve on its tower and on the
  lattice.
* **The Weil kernel of `ζ`.** The Hecke orbit kernel of a zero configuration and its index law, on
  `ℚ_{>0}`, on two primes and on `ℝ_{>0}`; the finite-index stratum, the Lindelöf law and the
  Krein–Langer structure with its converse; height truncations and integer windows; every
  receiver at every width bounded by the index; shrinking atoms reaching it; the quasi-analytic boundary of
  the receivers; the energy
  price of the index; heat collisions; the global law (the one-sided square-root count).
* **Prime towers and selectivity.** Tower kernels and the selectivity battery; selection of `Λ` by
  index zero; the one-prime law for `ζ`; local constituents and the pole principle; the margin
  `2 log 2` as the width of the index-one window of the atomic kernel, with a twin-blind index and
  a selective carrier.

See `HeckeKreinToeplitz/README.md`.
-/
