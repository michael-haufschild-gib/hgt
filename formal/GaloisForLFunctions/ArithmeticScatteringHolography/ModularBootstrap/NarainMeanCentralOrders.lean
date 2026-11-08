import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainCentralOrders
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanCentralJet

/-!
# Exact central orders of the averaged Narain transform

An analytic unit factorization and the two target orders classify the averaged central zero as simple, cubic or quintic.
-/

open Complex RHTower Filter Topology
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Every averaged transform has central order one, three or five, determined solely by exceptional heights. -/
theorem analyticOrderAt_narainMellinMean_zero (Y Z : Height) :
    analyticOrderAt (narainMellinMean Y Z) 0 =
      1 + (if Y = narainExceptionalHeight then 2 else 0) +
        (if Z = narainExceptionalHeight then 2 else 0) := by
  have hqorder : analyticOrderAt narainMeanCentralUnit 0 = 0 :=
    analyticAt_narainMeanCentralUnit_zero.analyticOrderAt_eq_zero.mpr (by rw [narainMeanCentralUnit_zero]; norm_num)
  have hid : AnalyticAt ℂ (fun u : ℂ => u) 0 := by fun_prop
  have hidorder : analyticOrderAt (fun u : ℂ => u) 0 = 1 := by
    apply (_root_.analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hid).mpr
    constructor
    · intro k hk
      have : k = 0 := by omega
      subst k
      rfl
    · norm_num [iteratedDeriv_fun_id]
  have hY := (differentiable_dividedFilledNumeratorMean Y).analyticAt 0
  have hZ := (differentiable_dividedFilledNumeratorMean Z).analyticAt 0
  rw [analyticOrderAt_congr (narainMellinMean_central_germ Y Z)]
  change analyticOrderAt ((((fun u : ℂ => u) * dividedFilledNumeratorMean Y) *
    dividedFilledNumeratorMean Z) * narainMeanCentralUnit) 0 = _
  rw [analyticOrderAt_mul ((hid.mul hY).mul hZ) analyticAt_narainMeanCentralUnit_zero, hqorder, add_zero,
    analyticOrderAt_mul (hid.mul hY) hZ, analyticOrderAt_mul hid hY, hidorder,
    analyticOrderAt_dividedFilledNumeratorMean_zero,
    analyticOrderAt_dividedFilledNumeratorMean_zero]

/-- The central zero is simple exactly when neither target height is exceptional. -/
theorem narainMellinMean_central_simple_iff (Y Z : Height) :
    analyticOrderAt (narainMellinMean Y Z) 0 = 1 ↔
      Y ≠ narainExceptionalHeight ∧ Z ≠ narainExceptionalHeight := by
  rw [analyticOrderAt_narainMellinMean_zero]
  by_cases hY : Y = narainExceptionalHeight <;>
    by_cases hZ : Z = narainExceptionalHeight <;> norm_num [hY, hZ]

/-- Order five occurs exactly at the pair of exceptional heights. -/
theorem narainMellinMean_central_order_five_iff (Y Z : Height) :
    analyticOrderAt (narainMellinMean Y Z) 0 = 5 ↔
      Y = narainExceptionalHeight ∧ Z = narainExceptionalHeight := by
  rw [analyticOrderAt_narainMellinMean_zero]
  by_cases hY : Y = narainExceptionalHeight <;>
    by_cases hZ : Z = narainExceptionalHeight <;> norm_num [hY, hZ]

#print axioms analyticOrderAt_narainMellinMean_zero
#print axioms narainMellinMean_central_simple_iff
#print axioms narainMellinMean_central_order_five_iff
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
