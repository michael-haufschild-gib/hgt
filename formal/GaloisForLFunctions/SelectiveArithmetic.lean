import GaloisForLFunctions.SelectiveArithmetic.TheMassOfAConductorPaysEveryDominatedContact
import GaloisForLFunctions.SelectiveArithmetic.ThePolarPacketsOfAWindow
import GaloisForLFunctions.SelectiveArithmetic.TheLiouvilleTwistFailsBeyondTheTrivialAperture
import GaloisForLFunctions.SelectiveArithmetic.TheHeightOfAPacketIsAMass
import GaloisForLFunctions.SelectiveArithmetic.CancellationInTheContactsBuysTheLadder
import GaloisForLFunctions.SelectiveArithmetic.AnIsolatedPairShowsAtTheRungOfItsDepth
import GaloisForLFunctions.SelectiveArithmetic.TheFeasibleSetsOfAConductor
import GaloisForLFunctions.SelectiveArithmetic.TheZerosOfADirichletLFunctionOnTheLadder
import GaloisForLFunctions.SelectiveArithmetic.TheSignIsSquareRootCancellationOfTheRieszMean
import GaloisForLFunctions.SelectiveArithmetic.EveryVisibleWeightIsBoundedByTheMass
import GaloisForLFunctions.SelectiveArithmetic.TheFirstSelectiveWindowOfZeta

/-!
# Selective Arithmetic

Umbrella for the theory of producers: which inequalities separate `ζ` and the true `L`-functions
from systems that share all their structures but one, to which scale a single structure proves a
sign, and where the first statement beyond that scale lies.

* The form of a system: contacts, conductor, archimedean symbol; dominated weight systems and
  feasible sets with a conductor.
* The Schur price of sizes and the trivial aperture of a conductor: the sign of the twisted part
  of the square of a quadratic ring up to the aperture `log log q − o(1)`, with a margin.
* The polar packets of a window: the even and the odd profile of the polar kernel, their masses
  and correlations.
* The fakes beyond the trivial aperture: the Liouville twist, the contacts of `1/ζ`, and the
  contacts of `ζ` without pole plane fail at aperture `log log q + o(1)`; the ladder of the
  conductor has no gap.
* The aspect of the height: a packet modulated to the height `t` carries the mass `log |t|`, the
  pole plane does not reach it, and Weil's form of `ζ` is positive there on packets of bounded
  shape up to the aperture `log log |t| − o(1)`.
* The exchange rate of the ladder on the prime side: a saving `n^{1/2 + γ}` in the partial sums of
  the contacts buys the sign up to the rung `κ < 1/(2γ)`.
* The exchange rate on the zero side: a lattice with the functional equation and one pair of depth
  `δ` is positive below the rung `κ = 1/(2δ)` and fails above it; in every configuration with a
  logarithmic local count, positivity on a rung forces an off-line companion of every zero deeper
  than the rung.
* The feasible sets of a conductor: finite determinacy, monotonicity in aperture and conductor,
  convexity; the trivial aperture as a threshold of the dominated box; a uniform floor is
  feasibility at a larger conductor.
* The zeros of a Dirichlet `L`-function on the ladder of its conductor: positivity below the rung
  one, companions of every zero deeper than a rung above it.
* The converse of the exchange rate on the prime side: the sign of a dominated system on the two
  polar packets of an aperture is square-root cancellation of the Riesz mean of its contacts at
  that scale; for a character it bounds `Σ Λ(n) Re χ(n) log(Y/n)`.
* The box law of a conductor: every visible weight of a feasible system is at most
  `√n (log q + log(1 + 4n) + C)`; an `ℓ¹` ball of the size of the mass is feasible; below the first
  contact the weights do not enter.
* The first selective window of `ζ`: with the pole plane, a window of ratio less than `2` is not
  selective; beyond it the weight at `2` is confined to an interval of half-length
  `√2 (log(1/r) + C)` that contains a neighbourhood of `log 2` up to the aperture `181/500`.

See `SelectiveArithmetic/README.md`.
-/
