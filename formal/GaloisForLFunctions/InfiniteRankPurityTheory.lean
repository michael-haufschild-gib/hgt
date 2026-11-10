import GaloisForLFunctions.InfiniteRankPurityTheory.ADefectOfIndexOneIsPureOffTheRealAxis
import GaloisForLFunctions.InfiniteRankPurityTheory.TheEisensteinConstantTermIsPureByParity
import GaloisForLFunctions.InfiniteRankPurityTheory.TheIndexBoundIsAttained
import GaloisForLFunctions.InfiniteRankPurityTheory.CesaroMeansReadTheModesOfASummableTower
import GaloisForLFunctions.InfiniteRankPurityTheory.BoundedIntegralTracesOfOneFrobeniusAreTorsion
import GaloisForLFunctions.InfiniteRankPurityTheory.TwoFrobeniiDetermineATraceClassModule
import GaloisForLFunctions.InfiniteRankPurityTheory.IntegralTraceClassModulesOverTheIntegersAreTate
import GaloisForLFunctions.InfiniteRankPurityTheory.AtPositiveWeightIntegralityDoesNotBoundTheRank
import GaloisForLFunctions.InfiniteRankPurityTheory.TheSymmetriesOfTheZerosAreTheTwoInvolutions
import GaloisForLFunctions.InfiniteRankPurityTheory.CesaroMeansOnThickSets
import GaloisForLFunctions.InfiniteRankPurityTheory.EliminationNeedsOnlyAnAttainedTop
import GaloisForLFunctions.InfiniteRankPurityTheory.NoTraceClassFamilyOfZerosIsIntegral
import GaloisForLFunctions.InfiniteRankPurityTheory.TheIndexIsSemicontinuous
import GaloisForLFunctions.InfiniteRankPurityTheory.TheLefschetzNumbersOfTheIntegersAreNotTraces
import GaloisForLFunctions.InfiniteRankPurityTheory.TheArchimedeanFibreIsATraceAndTheFiniteContactsAreNot
import GaloisForLFunctions.InfiniteRankPurityTheory.TheLineLawSeesTheStripAndNotTheLine
import GaloisForLFunctions.InfiniteRankPurityTheory.TheExceptionalParameterIsBornAtFourPiExpMinusGamma
import GaloisForLFunctions.InfiniteRankPurityTheory.ASchurFunctionReducesAtEveryNode
import GaloisForLFunctions.InfiniteRankPurityTheory.ADefectOfDegreeKappaHasAtMostKappaExceptionalPoints
import GaloisForLFunctions.InfiniteRankPurityTheory.OverTheIntegersEveryModeIsItsOwnConjugacyClass
import GaloisForLFunctions.InfiniteRankPurityTheory.KroneckerOverTheIntegersNeedsNoDistinctModes
import GaloisForLFunctions.InfiniteRankPurityTheory.AFamilySeesItsMeanAndItsMembersOfPositiveMass
import GaloisForLFunctions.InfiniteRankPurityTheory.WithoutTheChainConditionKroneckerOverTheIntegersFails
import GaloisForLFunctions.InfiniteRankPurityTheory.AModeAccessibleFromInfinityIsEliminated
import GaloisForLFunctions.InfiniteRankPurityTheory.OnTheFlowTheWeightFiltrationNeedsNoChainCondition
import GaloisForLFunctions.InfiniteRankPurityTheory.NoFamilyOfZerosIsIntegralWhateverTheirRealParts
import GaloisForLFunctions.InfiniteRankPurityTheory.TheZerosContainNoClassOfOneFrobenius

/-!
# Infinite-rank purity theory

Weil numbers without finite rank and without moduli: the infinite-rank counterpart of each
finite-rank purity mechanism, with its price, and the conversions from a statement in law to a
statement at a point.

* The index: a defect of degree `κ` has at most `κ` exceptional points, and at most `κ/2` above the
  real axis for real data; the bound is attained by every configuration. At index one: the line law
  of the Eisenstein constant term for every `Y ≥ 1`, with an exceptional parameter exactly for
  `Y > 4π e^{−γ}`. The index is semicontinuous at any index.
* The fixed part: the line law of a family holds over every finite configuration of zeros in the
  closed strip and over every limit of such, and fails over a non-real zero right of `Re = 1`; it
  does not see the line. Under a measure the fixed part is the mean of the family and the excess
  of the second moment over the variance; a member of positive mass is seen by amortization.
* Integrality: Kronecker's theorem for summable towers of one Frobenius, and for trace-class
  Frobenius modules over `ℤ` at any Frobenius with modes repeated at will (Tate twists only); a pure
  integral tower of infinite rank at positive weight; no family of distinct zeros of trace class of
  order two is integral, whatever the real parts of the zeros.
  Without the chain condition on the weights the theorem fails: the Wolff module has trace `1` at
  every Frobenius and a visible mode `5/4`.
* Trace class: traces determine the module and growth is the weight filtration at any Frobenius;
  on the whole flow, for locally finite modules, with no condition on the weights;
  the archimedean fibre is the module of even jets; `Λ`, the Mertens function, the prime counting
  function and the Lefschetz numbers of the glued square are not traces of any order.
* Elimination: window means on thick sets; an attained top suffices, at any rank; below the top an
  isolated mode accessible from infinity is eliminated by continuing the resolvent.
* Conjugacy: the affine and anti-affine symmetries of the zero divisor are `1, ι, c, ιc`; over `ℤ`
  an equivariant map is diagonal, the module is semisimple without multiplicity, and over one
  Frobenius conjugates share their weight. The zeros contain no class of one Frobenius:
  `Σ_n |ζ(ρ + inT)|/|ρ + inT|` diverges along every vertical progression in the strip, so `ξ`
  vanishes on the zeros of no local factor `q^{-s} - u` and of no curve over a finite field.

See `InfiniteRankPurityTheory/README.md`.
-/
