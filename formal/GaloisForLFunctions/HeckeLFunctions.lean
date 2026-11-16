import GaloisForLFunctions.HeckeLFunctions.ElementsPrimeToAModulusReduceModuloIt
import GaloisForLFunctions.HeckeLFunctions.TheRayClassGroupIsFinite
import GaloisForLFunctions.HeckeLFunctions.Characters.RestrictionFibers
import GaloisForLFunctions.HeckeLFunctions.Characters.ResidueExtensionCount
import GaloisForLFunctions.HeckeLFunctions.Characters.ClassTwistsPreserveLocalData
import GaloisForLFunctions.HeckeLFunctions.HeckeCharactersGiveConvergentLSeries
import GaloisForLFunctions.HeckeLFunctions.LatticeCosetsInSignedNormBalls
import GaloisForLFunctions.HeckeLFunctions.RayClassesOfPrincipalIdealsAreReadByResidues
import GaloisForLFunctions.HeckeLFunctions.IdealsOfARayClassAreConePoints
import GaloisForLFunctions.HeckeLFunctions.ConePointsOfARayClassAreLatticeCosets
import GaloisForLFunctions.HeckeLFunctions.IdealsAreEquidistributedInRayClasses
import GaloisForLFunctions.HeckeLFunctions.HeckeLFunctionsContinuePastTheLineReOne
import GaloisForLFunctions.HeckeLFunctions.NonzeroIdealsArePrimeExponentVectors
import GaloisForLFunctions.HeckeLFunctions.HeckeLSeriesHaveEulerProducts
import GaloisForLFunctions.HeckeLFunctions.HeckeEulerLogarithmsGiveTheThreeFourOneInequality
import GaloisForLFunctions.HeckeLFunctions.NonquadraticCharactersDoNotVanishOnTheLineReOne
import GaloisForLFunctions.HeckeLFunctions.TheTrivialCharacterRemovesTheModulusEulerFactors
import GaloisForLFunctions.HeckeLFunctions.TheTrivialCharacterHasAPositiveResidue
import GaloisForLFunctions.HeckeLFunctions.EveryRayResidueAndSignHasAnIntegralRepresentative
import GaloisForLFunctions.HeckeLFunctions.HeckeCharactersSplitIntoFiniteCharactersAndRealParities
import GaloisForLFunctions.HeckeLFunctions.HeckeIdealThetaIsUnitPeriodic
import GaloisForLFunctions.HeckeLFunctions.HeckeThetaHasAFiniteFourierTransform
import GaloisForLFunctions.HeckeLFunctions.HeckeThetaTailsDecayExponentially

/-!
# Hecke L-functions

Umbrella for the programme on Hecke L-functions of a number field `K`: moduli `𝔪 = 𝔪₀ 𝔪∞`, the
reduction of elements prime to `𝔪` to `(𝓞_K/𝔪₀)ˣ × {±1}^{𝔪∞}`, the ray group `K^{𝔪,1}_+`, the
finite ray class group `Cl_𝔪 = I^𝔪 / P_𝔪`, Hecke characters, their absolutely convergent prime-ideal
Euler products and nonvanishing on `Re s > 1`, the equidistribution of integral ideals in ray
classes with positive densities and power saving `O(x^{1−1/n})`, and the
continuation of `L(s, ψ)` to `Re s > 1 − 1/n` (holomorphic for `ψ ≠ 1`, `ρ_𝔪 ζ(s)` plus a holomorphic
function for `ψ = 1`). For the trivial character, deleting the finite-modulus Euler factors from
Dedekind zeta gives the positive residue `ρ_𝔪 = Res₁ ζ_K · ∏_{𝔭 ∣ 𝔪₀} (1 - 1/N𝔭)`.
Summable Euler logarithms give the three-four-one inequality. Positive occupation expansions
and Landau exclude quadratic zeros at one; together these prove nonvanishing for every character
on `Re s ≥ 1`, away from the trivial pole.
Positive signed-cone volumes and lattice counts also show that arbitrary invertible residues
and real sign patterns have nonzero integral representatives, making the ray reduction surjective.
Every Hecke character therefore splits on principal ideals into a finite residue character
and real-place parities; their product is trivial on global units.
The resulting finite-weighted parity theta series converges absolutely on every integral ideal
and is periodic under translation by global-unit place logarithms.
Residue-coset parity Poisson transforms this theta into an absolutely convergent sum on the
arithmetic trace-dual ideal, with explicit finite Fourier coefficients and exact normalization.
The physical and dual zero terms are classified; both remaining theta tails decay exponentially,
uniformly on bounded archimedean place profiles.
The actual theta Mellin pair has an entire regular part and explicit zero-mode residues.
Integration over the actual unit logarithm domain multiplies those zero modes by the regulator
and preserves the Mellin reflection. Nonzero ideal elements are indexed by inverse-class ideals
and global units; splitting units into torsion and logarithmic lattice coordinates expresses
the nonzero theta as an absolutely convergent sum of lattice periodizations with exact torsion factor.
Uniform summable Gaussian bounds justify unfolding its unit-domain average into whole-log-space
kernel integrals indexed by the inverse ordinary ideal class.
Each nonzero element kernel has an absolutely convergent Mellin integral with its actual
principal-ideal character coefficient and standard Gamma product, normalized by
`1/(degree * 2^unitRank)`. Its absolute Mellin mass separates into the norm of the ideal
summand and a common archimedean mass.
Absolute ideal-series convergence then justifies the infinite Mellin exchange, identifying
each continued unit theta transform with its inverse-class Hecke series on `Re s > 1`.
Finite ordinary-class recombination extends the full series meromorphically to the complex plane.
Entire divided differences remove the apparent poles for nontrivial characters; comparison with
the ideal-counting residue gives the trivial character a genuine simple pole at one and no others.
The global function agrees with the counting continuation on their common half-plane.
For nontrivial characters, harmonic ideal sums approach the value at one with a power saving,
and their logarithmically weighted versions remain bounded. The weighted ideal von Mangoldt
identity gives the exact prime-power hyperbola formula for these sums.
Nonvanishing at one then bounds the prime-power and prime-ideal Mertens sums for nontrivial
characters. For the trivial character, both sums are `log N + O(1)`.
-/
import GaloisForLFunctions.HeckeLFunctions.HeckeThetaHasMellinContinuation
import GaloisForLFunctions.HeckeLFunctions.HeckeThetaIsJointlyContinuous
import GaloisForLFunctions.HeckeLFunctions.HeckeThetaAveragesOverTheUnitDomain
import GaloisForLFunctions.HeckeLFunctions.NonzeroIdealElementsAreGlobalUnitOrbits
import GaloisForLFunctions.HeckeLFunctions.HeckeThetaUnitOrbitsAreLogPeriodizations
import GaloisForLFunctions.HeckeLFunctions.HeckeUnitOrbitsUnfoldOverTheLogSpace
import GaloisForLFunctions.HeckeLFunctions.HeckeThetaWeightsArePrincipalIdealCharacters
import GaloisForLFunctions.HeckeLFunctions.HeckeGammaFactorsAreArchimedeanMellinIntegrals
import GaloisForLFunctions.HeckeLFunctions.HeckeElementKernelsHaveExactMellinIntegrals
import GaloisForLFunctions.HeckeLFunctions.HeckeUnitAveragedMellinIsTheIdealClassSeries
import GaloisForLFunctions.HeckeLFunctions.UnramifiedHeckeCharactersDescendToIdealClasses
import GaloisForLFunctions.HeckeLFunctions.HeckeLSeriesAreFiniteSumsOfClassThetaTransforms
import GaloisForLFunctions.HeckeLFunctions.HeckeLFunctionsHaveGlobalContinuation
import GaloisForLFunctions.HeckeLFunctions.QuadraticHeckeProductsHavePositiveOccupationExpansions
import GaloisForLFunctions.HeckeLFunctions.HeckeLFunctionsDoNotVanishOnTheLineReOne
import GaloisForLFunctions.HeckeLFunctions.HeckeHarmonicSumsHavePowerSavingTails
import GaloisForLFunctions.HeckeLFunctions.HeckeHarmonicSumsSatisfyTheIdealHyperbolaIdentity
import GaloisForLFunctions.HeckeLFunctions.HeckeCharactersSatisfyMertensBounds
import GaloisForLFunctions.HeckeLFunctions.HeckeFiniteCharactersHavePrimitiveConductors
import GaloisForLFunctions.HeckeLFunctions.HeckeFiniteFourierCoefficientsAreGaussSums
import GaloisForLFunctions.HeckeLFunctions.HeckeFourierSupportIsIdealCoprimality
import GaloisForLFunctions.HeckeLFunctions.HeckeFourierCoefficientsScaleByRayResidues
import GaloisForLFunctions.HeckeLFunctions.HeckePrimitiveGaussConstantsHaveExactNorm
import GaloisForLFunctions.HeckeLFunctions.HeckeFourierCoefficientsAreInverseHeckeValues
import GaloisForLFunctions.HeckeLFunctions.HeckeConductorsAndParitiesAreInvariantUnderInversion
import GaloisForLFunctions.HeckeLFunctions.HeckeDualFrequenciesHaveClassGenerators
import GaloisForLFunctions.HeckeLFunctions.HeckeFieldElementKernelsHaveExactMellinIntegrals
import GaloisForLFunctions.HeckeLFunctions.HeckeDualThetaKernelsAreUnitCovariant
import GaloisForLFunctions.HeckeLFunctions.HeckeDualClassKernelsHaveExactMellinIntegrals
import GaloisForLFunctions.HeckeLFunctions.HeckeDualUnitOrbitsUnfoldOverTheLogSpace
import GaloisForLFunctions.HeckeLFunctions.HeckeDualAveragedMellinIsTheInverseClassSeries
import GaloisForLFunctions.HeckeLFunctions.HeckeCompletedThetaResiduesCancel
import GaloisForLFunctions.HeckeLFunctions.HeckeGammaCompletedFunctionsHaveRemovableValues
import GaloisForLFunctions.HeckeLFunctions.HeckeCompletionFactorsHaveExactArithmeticNormalization
import GaloisForLFunctions.HeckeLFunctions.PrimitiveHeckeLFunctionsHaveCompletedFunctionalEquation
import GaloisForLFunctions.HeckeLFunctions.ResidueCharactersTrivialOnUnitsAreHeckeCharacters
