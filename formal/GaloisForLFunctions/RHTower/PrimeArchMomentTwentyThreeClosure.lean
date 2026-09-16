import GaloisForLFunctions.RHTower.XiCenteredOrderTwentyFourSixthTraceClosure
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomHighOrderMomentBounds

/-!
# Unconditional closure of the twenty-third prime--Gamma moment

The order-twenty-four sector argument had reduced positivity of the twenty-third normalized
prime--Gamma moment to five explicit first-atom inequalities.  Those inequalities are already
certified by the exact high-order first-atom enclosure.  This module removes the residual
interface premises without inserting a zero table, a numerical approximation, or a new analytic
assumption.

The consequence is deliberately local: it adds one closed source moment.  It does not assert
global resolvent passivity, which remains an RH-strength statement.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- **Closed order-24 source consequence.**  The exact first-atom enclosure closes the remaining
sector alternative, so the normalized prime--Gamma moment of index twenty-three is strictly
positive without hypotheses. -/
theorem normalizedPrimeArchMoment_twentyThree_pos :
    0 < normalizedPrimeArchMoment 23 := by
  obtain ⟨h0, h1lower, h1upper, h2, h3⟩ :=
    thetaCuspFirstAtom_highOrder_five_bounds
  exact normalizedPrimeArchMoment_twentyThree_pos_of_firstAtom_bounds
    h0 h1lower h1upper h2 h3

end

end RHTower
