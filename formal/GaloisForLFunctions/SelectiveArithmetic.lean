import GaloisForLFunctions.SelectiveArithmetic.TheMassOfAConductorPaysEveryDominatedContact
import GaloisForLFunctions.SelectiveArithmetic.ThePolarPacketsOfAWindow
import GaloisForLFunctions.SelectiveArithmetic.TheLiouvilleTwistFailsBeyondTheTrivialAperture
import GaloisForLFunctions.SelectiveArithmetic.TheHeightOfAPacketIsAMass
import GaloisForLFunctions.SelectiveArithmetic.CancellationInTheContactsBuysTheLadder
import GaloisForLFunctions.SelectiveArithmetic.AnIsolatedPairShowsAtTheRungOfItsDepth
import GaloisForLFunctions.SelectiveArithmetic.TheFeasibleSetsOfAConductor

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
  convexity; the trivial aperture as a threshold of the dominated box.

See `SelectiveArithmetic/README.md`.
-/
