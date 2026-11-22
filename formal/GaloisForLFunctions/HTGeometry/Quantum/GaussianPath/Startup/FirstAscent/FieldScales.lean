import Mathlib.Data.Nat.Log
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-! # Scales for the prefix size and the number of selected sites -/
open Filter
namespace GaloisForLFunctions.HTGeometry.FirstAscent

/-- Index of the largest complete group of 8ʲ pairs in a prefix. -/
def pairScale (n : ℕ) := Nat.log 8 ((n+2)/2)

theorem tendsto_pairScale : Tendsto pairScale atTop atTop := by
  rw [tendsto_atTop]
  intro k
  refine eventually_atTop.2 ⟨2*8^k,fun n hn => ?_⟩
  exact Nat.le_log_of_pow_le (by decide) (by omega)

theorem pairScale_bounds (n : ℕ) :
    2*8^pairScale n ≤ n+2 ∧ n+2 ≤ 16*8^pairScale n := by
  have hlo := Nat.pow_log_le_self 8 (show (n+2)/2≠0 by omega)
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1<8) ((n+2)/2)
  rw [pow_succ] at hhi
  unfold pairScale
  omega

/-- The chosen field scale h controls N/s from both sides, and there are
enough complete pairs to allow s selected sites at that scale. -/
theorem exists_budget_scale {n s H : ℕ} (hs : 0<s) (hsize : 16*8^H*s ≤ n+2) :
    ∃ h : ℕ, H ≤ h ∧ h ≤ pairScale n ∧ s*8^h ≤ 8^pairScale n ∧ n+2 ≤ 16*8^(h+1)*s := by
  let m := 8^pairScale n
  have hn : n+2 ≤ 16*m := (pairScale_bounds n).2
  have hH : 8^H*s ≤ m := by
    have hh := hsize.trans hn
    rw [Nat.mul_assoc] at hh
    omega
  have hq : 8^H ≤ m/s := (Nat.le_div_iff_mul_le hs).mpr hH
  have hp : 0 < m/s := (pow_pos (by decide : 0<(8:ℕ)) H).trans_le hq
  let h := Nat.log 8 (m/s)
  have hh : 8^h ≤ m/s := Nat.pow_log_le_self 8 hp.ne'
  have hfit := (Nat.le_div_iff_mul_le hs).mp hh
  have htop := Nat.lt_pow_succ_log_self (by decide : 1<8) (m/s)
  have hnext : m < 8^(h+1)*s := (Nat.div_lt_iff_lt_mul hs).mp htop
  refine ⟨h,Nat.le_log_of_pow_le (by decide) hq,?_,by simpa only [Nat.mul_comm] using hfit,?_⟩
  · exact (Nat.pow_le_pow_iff_right (by decide : 1<8)).mp (hh.trans (Nat.div_le_self m s))
  · exact hn.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 16 hnext.le)

end GaloisForLFunctions.HTGeometry.FirstAscent
