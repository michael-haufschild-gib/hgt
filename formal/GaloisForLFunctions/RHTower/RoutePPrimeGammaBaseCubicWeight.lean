import GaloisForLFunctions.RHTower.RoutePPrimeGammaCubicCarrierIdentification
import GaloisForLFunctions.RHTower.RoutePPrimitiveBaseCauchyCapacityReduction

/-!
# Route-P natural base cubic weight

Narrow arithmetic interface between the natural-number prime--Gamma carrier and the primitive
Route-P base Cauchy budget.  This module isolates the reusable weight identities from the broader
CCM Green-source bridge.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Natural-number form of the undifferenced Route-P base Cauchy mass. -/
def routePPrimeGammaBaseCubicWeight (n : ℕ) : ℝ :=
  (216 / 115 : ℝ) * routePPrimeGammaCubicWeight n

/-- Prime-power valuation preserves the complete base mass, including prime label and depth. -/
theorem routePPrimeGammaBaseCubicWeight_valuation
    (pe : Nat.Primes × ℕ) :
    routePPrimeGammaBaseCubicWeight (xiGammaEulerValuationNat pe) =
      routePPrimitiveBaseCauchyCubicWeight pe := by
  rw [routePPrimeGammaBaseCubicWeight,
    routePPrimeGammaCubicWeight_valuation,
    routePPrimitiveBaseCauchyCubicWeight]

theorem summable_routePPrimeGammaBaseCubicWeight :
    Summable routePPrimeGammaBaseCubicWeight := by
  exact summable_routePPrimeGammaCubicWeight.mul_left (216 / 115 : ℝ)

/-- The full natural-number Green mass is exactly the P-G181 primitive base budget. -/
theorem tsum_routePPrimeGammaBaseCubicWeight_eq_budget :
    ∑' n : ℕ, routePPrimeGammaBaseCubicWeight n =
      routePPrimitiveBaseCauchyCubicTraceBudget := by
  change (∑' n : ℕ, (216 / 115 : ℝ) * routePPrimeGammaCubicWeight n) = _
  rw [tsum_mul_left]
  rw [← routePPrimitiveCollisionCubicTraceBudget_eq_primeGamma,
    ← routePPrimitiveBaseCauchyCubicTraceBudget_eq]

/-- The natural/primitive source mass retains the established two-unit bound. -/
theorem tsum_routePPrimeGammaBaseCubicWeight_lt_two :
    (∑' n : ℕ, routePPrimeGammaBaseCubicWeight n) < 2 := by
  rw [tsum_routePPrimeGammaBaseCubicWeight_eq_budget]
  exact routePPrimitiveBaseCauchyCubicTraceBudget_lt_quantum

end

end RHTower
