import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheCubicEisensteinSeriesUnfolds
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheIncompleteEisensteinSeriesReadsTheConstantTerm
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheConstantTermContinuesAcrossFourThirds
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheSquareOfTheCubicThetaUnfolds
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheSquareOfTheSourceThetaUnfolds
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheCubeFrequenciesOfTheThetaSquareFactorOut
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheCuspHeightsOfAPointAreSparse
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheThetaCoefficientsHaveTheHeckeBound
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheMellinTransformOfTheThetaSquareReadsItsDirichletSeries
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheEisensteinPairingContinuesAcrossFourThirds
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheThetaSquareHasARationalCuspSubtraction
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheRationalCuspSubtractionScatters
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheRenormalizedThetaSquareIsBounded
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheRenormalizedThetaSquareUnfolds
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheSquaredThetaSeriesHasADoublePole
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheSquaredThetaSeriesSplitsIntoNineTwists
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheTwistedSquarefreeCombinationHasASimplePole
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheRotatedCorrelationsSeeOnlyTheThreeDivisibleLayer

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
`|T_s(h)| ≤ C(1 + |ξ_h|)` for the projected theta coefficients; the Mellin transform of the nonconstant part of the constant
term of `θ_s²` as `M(s) Σ_{h≠0} T_s(h)² (4π|ξ_h|)^{−s}`; the Eisenstein pairing split into a seed
term and an `L²` correction with at most a simple pole at `4/3`; the rational cusp subtraction of
`θ_s²` and the Mellin transform of its scattering; boundedness and square integrability of the
renormalized `θ_s² − H`; the continuation of `M(s) Σ_{h≠0} T_s(h)² (4π|ξ_h|)^{−s}` to
`{1 < Re s < 13/3, Im s > 0}` and its double pole at `4/3` with leading coefficient `108π³r³`; the
twisted multiplicativity of the theta coefficients across `h = u λ^m gen I`, the split of the squared
series into twisted squarefree series times `Z₀(3s/2 − 1)`, and the simple pole of their combination. See `SpectralTheoryOfTheCubicCover/README.md`.
-/
