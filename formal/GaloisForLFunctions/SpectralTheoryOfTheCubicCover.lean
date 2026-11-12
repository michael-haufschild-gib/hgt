import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheCubicEisensteinSeriesUnfolds
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheIncompleteEisensteinSeriesReadsTheConstantTerm
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheConstantTermContinuesAcrossFourThirds
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheSquareOfTheCubicThetaUnfolds
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheSquareOfTheSourceThetaUnfolds
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheCubeFrequenciesOfTheThetaSquareFactorOut
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheCuspHeightsOfAPointAreSparse
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheThetaCoefficientsHaveTheHeckeBound

/-!
# Spectral Theory of the Cubic Cover

Umbrella for the Rankin–Selberg layer over the cubic metaplectic cover of `SL₂` over `ℚ(ζ₃)`:
unfolding of the incomplete and complete cubic Eisenstein series against functions of multiplier
`κ⁻¹`, the period strip as a strict fundamental set of the cusp stabilizer, and the pairing of a
height profile with the constant term; the constant term of the cubic Eisenstein series continued
across `4/3`, its residue and the logarithm in its Laurent coefficient; the constant term of `θ²`
and the Rankin–Selberg identity of `θ²` and of the projected `θ_s²` against incomplete Eisenstein
series; the factorization of the Dirichlet series of the squared theta coefficients through
`ζ_K(3w − 1)`; the count of cusp cosets lifting a point to height `≥ Y`, and the Hecke bound
`|T_s(h)| ≤ C(1 + |ξ_h|)` for the projected theta coefficients. See `SpectralTheoryOfTheCubicCover/README.md`.
-/
