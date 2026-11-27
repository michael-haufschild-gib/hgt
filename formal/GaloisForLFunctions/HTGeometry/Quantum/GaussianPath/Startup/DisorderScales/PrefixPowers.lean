import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Tactic

/-! # Polynomial scales for prefixes of one infinite chain -/
open Filter
namespace GaloisForLFunctions.HTGeometry

/-- Largest j among the first n+1 integers with room for four jᵖ rows. -/
def powerPrefixIndex (p n : ℕ) := Nat.findGreatest (fun j => 4*j^p≤n+1) (n+1)

theorem powerPrefixIndex_tendsto (p : ℕ) : Tendsto (powerPrefixIndex p) atTop atTop := by
  apply tendsto_atTop.mpr
  intro a
  filter_upwards [eventually_ge_atTop (max a (4*a^p))] with n hn
  exact Nat.le_findGreatest (P:=fun j => 4*j^p≤n+1)
    ((le_max_left _ _).trans (hn.trans (Nat.le_succ n)))
    ((le_max_right _ _).trans (hn.trans (Nat.le_succ n)))

/-- Both neighboring tests use the same prefix, including boundary rows. -/
theorem powerPrefixIndex_bounds (p n : ℕ) (hp : 0<p) (hn : 3≤n) :
    let j := powerPrefixIndex p n
    0<j ∧ 4*j^p≤n+1 ∧ n+2≤4*(2*j)^p := by
  intro j
  have hroom : 4*1^p≤n+1 := by simpa only [one_pow,mul_one] using (show 4≤n+1 by omega)
  have hj : 1≤j := Nat.le_findGreatest (P:=fun k => 4*k^p≤n+1) (by omega : 1≤n+1) hroom
  have hlo : 4*j^p≤n+1 := Nat.findGreatest_spec (P:=fun k => 4*k^p≤n+1) (by omega : 1≤n+1) hroom
  have hjn : j≤j^p := by simpa only [pow_one] using pow_le_pow_right₀ hj hp
  have hnext : ¬4*(j+1)^p≤n+1 := Nat.findGreatest_is_greatest (P:=fun k => 4*k^p≤n+1)
    (show powerPrefixIndex p n<j+1 from Nat.lt_succ_self _) (by omega)
  exact ⟨hj,hlo,(show n+2≤4*(j+1)^p by omega).trans
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (by omega : j+1≤2*j) _))⟩

end GaloisForLFunctions.HTGeometry
