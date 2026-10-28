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
import GaloisForLFunctions.HeckeLFunctions.TheTrivialCharacterRemovesTheModulusEulerFactors

/-!
# Hecke L-functions

Umbrella for the programme on Hecke L-functions of a number field `K`: moduli `𝔪 = 𝔪₀ 𝔪∞`, the
reduction of elements prime to `𝔪` to `(𝓞_K/𝔪₀)ˣ × {±1}^{𝔪∞}`, the ray group `K^{𝔪,1}_+`, the
finite ray class group `Cl_𝔪 = I^𝔪 / P_𝔪`, Hecke characters and their L-series, and the
equidistribution of integral ideals in ray classes with power saving `O(x^{1−1/n})`, and the
continuation of `L(s, ψ)` to `Re s > 1 − 1/n` (holomorphic for `ψ ≠ 1`, `ρ_𝔪 ζ(s)` plus a holomorphic
function for `ψ = 1`).
-/
