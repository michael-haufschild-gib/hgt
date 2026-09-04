import GaloisForLFunctions.RHTower.RestrictedUnitaryCubicRelativeIndex
import GaloisForLFunctions.RHTower.SourceHorizontalWoldBVCompleteSplitPrimitiveBudgetFirewall

/-!
# Final strict-subunit certificate for the restricted-unitary cubic source

Kept separate from the analytic core because the sharp symbolic prime bound has a large,
independent source-horizontal dependency graph.  No estimate is reproved here: this module joins
the checked exact natural-number identity to its existing sharp `< 1` theorem.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap
open scoped BigOperators

/-- Exact source identity and strict subunit bound for the complete cubic Route-P budget. -/
theorem restrictedUnitaryCubic_sourceBudget_closed :
    (∑' n : ℕ, routePPrimeGammaBaseCubicWeight n) =
        routePPrimitiveBaseCauchyCubicTraceBudget ∧
      routePPrimitiveBaseCauchyCubicTraceBudget < 1 := by
  exact ⟨tsum_routePPrimeGammaBaseCubicWeight_eq_budget,
    routePPrimitiveBaseCauchyCubicTraceBudget_lt_one⟩

/-- Closed final RUCRI certificate joining operator algebra, all analytic source identities, and
the sharp symbolic subunit bound. -/
theorem restrictedUnitaryCubicRelativeIndex_fully_closed :
    RestrictedUnitaryCubicRelativeIndexAlgebraStatement ∧
      routePPrimitiveBaseCauchyCubicTraceBudget < 1 := by
  exact ⟨restrictedUnitaryCubicRelativeIndex_algebra_closed,
    routePPrimitiveBaseCauchyCubicTraceBudget_lt_one⟩

end RHTower
