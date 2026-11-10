import GaloisForLFunctions.ConstituentTheoryOfTheZeros.TheJumpLawHoldsOnEveryStripAboutTheLine
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.TheWienerAlgebraOfAStrip
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.WienersLemmaOnAStrip
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.TheLogarithmicDerivativeExpandsInAZeroFreeStrip
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.DirichletSeriesAreExpansionsOverThePositiveRationals
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.NoAbsolutelyConvergentDirichletSeriesIsAConstituent
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.ApproximantsThatShareZerosInGrowingBoxesLoseTheirZeros
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.NoAbsolutelyConvergentExpansionIsAConstituentInAStrip
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.SizesOnACircleCertifyTheDefectInside

/-!
# Constituent theory of the zeros

Which functions with an arithmetic expansion can share zeros with `ξ`: exactly, on a half-plane,
in a strip, in a box, in the limit. Every statement is pointwise and uses no sign of a form and no
operator.

* The jump law of the fractional part holds on every strip about the critical line with arbitrary
  positive scales on both sides; two expansions of one function on the two sides of the line carry
  the same weight at every scale, and the zeros of `ζ` cancel no pole between them
  (`TheJumpLawHoldsOnEveryStripAboutTheLine`).
* The absolutely convergent expansions over the positive rationals on a closed strip form a
  Banach algebra (`TheWienerAlgebraOfAStrip`) with Wiener's lemma: bounded below on the strip
  implies invertible (`WienersLemmaOnAStrip`); a zero-free expansion is invertible on closed
  substrips and its logarithmic derivative expands there, with zeros allowed on both sides
  (`TheLogarithmicDerivativeExpandsInAZeroFreeStrip`).
* No absolutely convergent Dirichlet series is a constituent with a zero: if its zeros in a
  half-plane containing the line, or only in a strip about the line, are zeros of `ξ`, it has none
  there (`NoAbsolutelyConvergentDirichletSeriesIsAConstituent`); the same for every absolutely
  convergent expansion over the positive rationals on a strip, with scales of both sizes
  (`NoAbsolutelyConvergentExpansionIsAConstituentInAStrip`).
* Approximants that converge in the norm of absolute convergence and share zeros with `ξ` in
  growing boxes have, from some index on, no zero near the line at any height; for Dirichlet
  polynomials of bounded length the height of the first zero that is not a zero of `ξ` is bounded
  in terms of the length (`ApproximantsThatShareZerosInGrowingBoxesLoseTheirZeros`).
* The index law in a window: if `‖E'‖ ≤ ‖E‖` on a circle, `E − E'` has at most as many zeros
  inside as `E`, with no winding number (`SizesOnACircleCertifyTheDefectInside`).
-/
