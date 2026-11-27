import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Tactic

/-! # Reciprocal dates covering every sufficiently long physical prefix -/

open Filter
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer

/-- Inverse startup date chosen from the number of disjoint four-row trials. -/
def prefixIndex (n : ℕ) := Nat.findGreatest (fun j => 4*j^256≤n+1) (n+1)

theorem prefixIndex_tendsto : Tendsto prefixIndex atTop atTop := by
  apply tendsto_atTop.mpr
  intro a
  filter_upwards [eventually_ge_atTop (max a (4*a^256))] with n hn
  exact Nat.le_findGreatest (P:=fun j => 4*j^256≤n+1)
    ((le_max_left _ _).trans (hn.trans (Nat.le_succ n)))
    ((le_max_right _ _).trans (hn.trans (Nat.le_succ n)))

/-- The smallest tested prefix has j²⁵⁶ boxes and even the largest
prefix at this date has at most 4(2j)²⁵⁶ sites. -/
theorem prefixIndex_bounds (n : ℕ) (hn : 3≤n) :
    let j := prefixIndex n
    0<j ∧ 4*j^256≤n+1 ∧ n+2≤4*(2*j)^256 := by
  intro j
  have hj : 1≤j := Nat.le_findGreatest (P:=fun k => 4*k^256≤n+1) (by omega : 1≤n+1) (by simpa using (show 4≤n+1 by omega))
  have hlo : 4*j^256≤n+1 := Nat.findGreatest_spec (P:=fun k => 4*k^256≤n+1)
    (Nat.zero_le _) (by simp)
  have hjn : j≤j^256 := by simpa only [pow_one] using pow_le_pow_right₀ hj (by decide : 1≤256)
  have hnxt : ¬4*(j+1)^256≤n+1 := Nat.findGreatest_is_greatest (P:=fun k => 4*k^256≤n+1)
    (show prefixIndex n<j+1 from Nat.lt_succ_self _) (by omega)
  exact ⟨hj,hlo,(show n+2≤4*(j+1)^256 by omega).trans
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (by omega : j+1≤2*j) _))⟩

end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
