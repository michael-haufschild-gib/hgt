import GaloisForLFunctions.ConstituentTheoryOfTheZeros.TheJumpLawHoldsOnEveryStripAboutTheLine
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.TheJumpLawOnAStripSurvivesSummablePoles
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.TheJumpLawOnAStripSurvivesFinitelyManyPoles
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.TheWienerAlgebraOfAStrip
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.WienersLemmaOnAStrip
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.TheLogarithmicDerivativeExpandsInAZeroFreeStrip
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.DirichletSeriesAreExpansionsOnTheScalesOneOverN
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.NoAbsolutelyConvergentDirichletSeriesIsAConstituent
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.NoAbsolutelyConvergentExpansionIsAConstituentInAStrip
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.InfinitelyManyZerosOfAnExpansionAreNotZerosOfXi
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.SummableResidueErrorsDoNotPermitZeros
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.OffLineZerosForceNonsummableResidues
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.WienerZeroDivisorsHaveBoundedLocalMass
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.VanishingZeroDisplacementsForcePurity
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.WienerZeroDivisorsResistSummableTransport
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.ApproximantsThatShareZerosInGrowingBoxesLoseTheirZeros
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.EveryBoxHasADirichletPolynomialWithExactlyTheZerosOfXi
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.ABoundedConstituentLivesInTheBohrStrip
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.PureDivisorsAreConstantInADisc
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.BoundedDirichletTwists
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.PrimeCutoffMultipliers
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.PoissonExtensionOfHolomorphicFamilies
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.PrimeContractionOfBoundedDirichletSeries
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.ABoundedConstituentHasNoZeros
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.SizesOnACircleCertifyTheDefectInside
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.ConsecutivePointsOfAProgressionDetectAPolynomial
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.TheJumpLawIsTheLawOfTheCarry

/-!
# Constituent theory of the zeros

Which functions with an expansion `Σ c(q) q^s` over positive real scales can share zeros with
`ξ`: exactly, on a half-plane, in a strip, in a box, in the limit. Every statement is pointwise
and uses no sign of a form and no operator.

* The jump law of the fractional part holds on every strip about the critical line with arbitrary
  positive scales on both sides; two expansions of one function on the two sides of the line carry
  the same weight at every scale, and the zeros of `ζ` cancel no pole between them
  (`TheJumpLawHoldsOnEveryStripAboutTheLine`), not even up to poles with summable residues
  (`TheJumpLawOnAStripSurvivesSummablePoles`, `TheJumpLawOnAStripSurvivesFinitelyManyPoles`).
* The absolutely convergent expansions over the positive reals on a closed strip form a Banach
  algebra (`TheWienerAlgebraOfAStrip`) with Wiener's lemma: bounded below on the strip implies
  invertible (`WienersLemmaOnAStrip`); a zero-free expansion is invertible on closed substrips and
  its logarithmic derivative expands there, with zeros allowed on both sides
  (`TheLogarithmicDerivativeExpandsInAZeroFreeStrip`).
* No absolutely convergent Dirichlet series is a constituent with a zero: if its zeros in a
  half-plane containing the line, or only in a strip about the line, are zeros of `ξ`, it has none
  there (`DirichletSeriesAreExpansionsOnTheScalesOneOverN`,
  `NoAbsolutelyConvergentDirichletSeriesIsAConstituent`). The same holds for every almost periodic
  function with an absolutely convergent expansion on a strip, exponential polynomials with real
  frequencies among them (`NoAbsolutelyConvergentExpansionIsAConstituentInAStrip`).
* If such a function has a zero in the strip, infinitely many of its zeros there are not zeros of
  `ξ` (`InfinitelyManyZerosOfAnExpansionAreNotZerosOfXi`).
  Their multiplicity-weighted zeta residues have divergent total norm, with no purity assumption
  (`SummableResidueErrorsDoNotPermitZeros`, `OffLineZerosForceNonsummableResidues`).
  Cofinite transport of the strip zeros to zeta zeros is impossible with `ℓᵖ` displacements
  for every finite `p > 0` (`WienerZeroDivisorsResistSummableTransport`).
* Approximants that converge in the norm of absolute convergence and share zeros with `ξ` in
  growing boxes have, from some index on, no zero near the line at any height; for Dirichlet
  polynomials of bounded length the height of the first zero that is not a zero of `ξ` is bounded
  in terms of the length (`ApproximantsThatShareZerosInGrowingBoxesLoseTheirZeros`).
* A box alone constrains nothing: for every height there is a Dirichlet polynomial whose zeros
  below that height are exactly the zeros of `ξ`, and its length is unbounded in the height
  (`EveryBoxHasADirichletPolynomialWithExactlyTheZerosOfXi`).
* Bohr's inequality: a Dirichlet series bounded on `Re s > x` converges absolutely on
  `Re s > x + ½`, and on `Re s > x` when its coefficients live on finitely many primes. So a
  bounded constituent with a zero needs infinitely many primes and `0 ≤ x < ½`
  (`ABoundedConstituentLivesInTheBohrStrip`).
* Bohr's inequality over a thin support: the two abscissas differ by at most half the exponent of
  convergence of the support (same module).
* The index law in a window: if `‖E'‖ ≤ ‖E‖` on a circle, `E − E'` has at most as many zeros
  inside as `E`, with no winding number; for a splitting `ξ = E + E^♯` the zeros of `ξ` in the
  disc are bounded by the defect (`SizesOnACircleCertifyTheDefectInside`).
* Turán's power sums: an exponential polynomial of `N` terms is detected on any `N` consecutive
  points of a vertical progression, with a constant free of the frequencies; `N` consecutive
  zeros on a progression force a zero on it that is not a zero of `ξ`
  (`ConsecutivePointsOfAProgressionDetectAPolynomial`).
* The jump law is the law of the carry `{x} + {y} − {x + y}`: the expansions on the two sides of
  the line have the same carries, and the carries determine the series
  (`TheJumpLawIsTheLawOfTheCarry`).
-/
