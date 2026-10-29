import GaloisForLFunctions.HeckeLFunctions.ElementsPrimeToAModulusReduceModuloIt
import GaloisForLFunctions.HeckeLFunctions.TheRayClassGroupIsFinite
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
Summable Euler logarithms give the three-four-one inequality; combined with continuation,
it proves that every nonquadratic character has no zeros on `Re s ≥ 1`.
Positive signed-cone volumes and lattice counts also show that arbitrary invertible residues
and real sign patterns have nonzero integral representatives, making the ray reduction surjective.
Every Hecke character therefore splits on principal ideals into a finite residue character
and real-place parities; their product is trivial on global units.
-/
