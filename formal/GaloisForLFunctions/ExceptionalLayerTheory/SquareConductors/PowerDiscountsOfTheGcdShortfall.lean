import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.CumulativePowerDiscount
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.CumulativeQuadratureOfTheGcdDeficit
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheGcdDeficitAtTheEighthPowerEndpoints

/-!
# The critical power discount for accumulated gcd shortfall

The power-integral alternative in Fino and Majdoub (arXiv:2611.24340,
Lemma 2.1) applies in cumulative shortfall coordinates. Discounting each
charge by (1+D) to the power p yields a finite total exactly when p>1
or the entire grid already has finite shortfall. At the eighth powers
the second possibility is excluded by the arithmetic half-step law.
-/

noncomputable section
open Finset Filter Set
open scoped Topology
open GaloisForLFunctions.CumulativeQuadrature

namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem mass_nonneg (r i : ℕ) : 0 ≤ powerGridGcdDeficit r i :=
  sum_nonneg fun _ _ => le_max_right _ _

/-- The complete supercritical tail is bounded by the remaining power
integral even when some steps vanish. -/
theorem supercritical_gcd_tail (r K : ℕ) {p : ℝ} (hp : 1 < p) :
    Summable (fun i => powerCharge (powerGridGcdDeficit r) p (K+i)) ∧
      (∑' i, powerCharge (powerGridGcdDeficit r) p (K+i)) ≤
        (1+powerGridGcdDeficit r K)^(1-p)/(p-1) := by
  let x := powerGridGcdDeficit r
  have hnn (i : ℕ) : 0 ≤ powerCharge x p (K+i) :=
    mul_nonneg (gcd_deficit_increment_bounds r _).1
      (Real.rpow_nonneg (add_nonneg zero_le_one (mass_nonneg r _)) _)
  have h := power_prefix_bound (monotone_gcd_deficit r) (mass_nonneg r 0) K (p := p)
  exact ⟨summable_of_sum_range_le hnn (fun n => h n hp),
    Real.tsum_le_of_sum_range_le hnn (fun n => h n hp)⟩

/-- On every power grid the only exception to the critical power law is
a finite total shortfall. This also holds under logarithmic discounting
at the critical reciprocal weight. -/
theorem gcd_discounts_summable_iff (r : ℕ) (p : ℝ) :
    (Summable (powerCharge (powerGridGcdDeficit r) p) ↔
      1 < p ∨ BddAbove (Set.range (powerGridGcdDeficit r))) ∧
    (Summable (logPowerCharge (powerGridGcdDeficit r) p) ↔
      1 < p ∨ BddAbove (Set.range (powerGridGcdDeficit r))) := by
  have hm (i : ℕ) := (gcd_deficit_increment_bounds r i).2
  exact ⟨summable_power_charge_iff (monotone_gcd_deficit r) (mass_nonneg r 0) hm p,
    summable_log_power_charge_iff (monotone_gcd_deficit r) (mass_nonneg r 0) hm p⟩

/-- The eighth-power arithmetic series converges precisely above the critical
discount. At equality the reciprocal logarithmic divergence persists. -/
theorem eighth_power_discount_summable_iff (p : ℝ) :
    (Summable (powerCharge (powerGridGcdDeficit 8) p) ↔ 1 < p) ∧
    (Summable (logPowerCharge (powerGridGcdDeficit 8) p) ↔ 1 < p) := by
  suffices hn : ¬ BddAbove (Set.range (powerGridGcdDeficit 8)) by
    obtain ⟨hp,hl⟩ := gcd_discounts_summable_iff 8 p
    simpa only [hn,or_false] using And.intro hp hl
  rintro ⟨B,hB⟩
  obtain ⟨c,hc⟩ := eighth_gcd_deficit_centered_converges
  have hlog : Tendsto (fun k : ℕ => Real.log k) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨k,h₁,h₂⟩ := ((hc.eventually_const_lt (sub_one_lt c)).and
    (hlog.eventually_gt_atTop (2*(B-c+1)))).exists
  linarith only [h₁,h₂,hB (mem_range_self k)]

#print axioms supercritical_gcd_tail
#print axioms gcd_discounts_summable_iff
#print axioms eighth_power_discount_summable_iff

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
