import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic

/-! # Counting large changes in a bounded monotone sequence of budgets -/
open Finset
namespace GaloisForLFunctions.HTGeometry.AccuracyScales

/-- Multiplicative increases at selected steps accumulate even across gaps. -/
private theorem paid_steps (r : ℕ) (f : ℕ → ℕ) (hm : Monotone f)
    (bad : ℕ → Prop) [DecidablePred bad] (hstep : ∀ i, bad i → r*f i ≤ f (i+1)) (L : ℕ) :
    r^((range L).filter bad).card*f 0 ≤ f L := by
  induction L with
  | zero => simp
  | succ k ih =>
    by_cases h : bad k
    · have hmem : k ∉ (range k).filter bad := fun hh => notMem_range_self (mem_filter.mp hh).1
      rw [range_add_one,filter_insert,if_pos h,card_insert_of_notMem hmem,pow_succ,Nat.mul_right_comm]
      exact (Nat.mul_le_mul_right r ih).trans ((Nat.mul_comm _ _).trans_le (hstep k h))
    · rw [range_add_one,filter_insert,if_neg h]
      exact ih.trans (hm (Nat.le_succ k))

/-- Each exceptional step increases the jth power of the budget by at least
a factor B. The range from B to B³ pays for at most 2j such steps. -/
theorem large_step_count (B : ℕ) (hB : 0 < B) (m : ℕ → ℕ) (hm : Monotone m)
    (hlo : ∀ i, B ≤ m i) (hhi : ∀ i, m i ≤ B^3) (j : ℕ) (hj : 1 ≤ j) (L : ℕ) :
    ((range L).filter (fun i => m i^j < m (i+1)^(j-1))).card ≤ 2*j := by
  by_cases hb : B = 1
  · have hone (i) : m i = 1 := le_antisymm (by simpa only [hb,one_pow] using hhi i)
      (by simpa only [hb] using hlo i)
    simp only [hone,one_pow,lt_self_iff_false,filter_false,card_empty,Nat.zero_le]
  let bad := fun i => m i^j < m (i+1)^(j-1)
  let count := ((range L).filter bad).card
  have hh := paid_steps B (fun i => m i^j) (fun _ _ h => Nat.pow_le_pow_left (hm h) j) bad
    (fun i h => (Nat.mul_le_mul (hlo _) h.le).trans_eq (by
      rw [Nat.mul_comm,←pow_succ,show j-1+1=j by omega])) L
  have h : B^(count+j) ≤ B^(3*j) := by
    rw [pow_add, pow_mul]
    exact ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hlo 0) j)).trans hh).trans
      (Nat.pow_le_pow_left (hhi L) j)
  have he := (Nat.pow_le_pow_iff_right (by omega : 1 < B)).mp h
  change count ≤ 2*j
  omega

/-- If the smallest budget is at least B and the largest at most B³, with
B ≤ 2^b, there can be at most 2b doublings. -/
theorem doubling_count {B b : ℕ} (hB : 0 < B) (hsize : B ≤ 2^b) (m : ℕ → ℕ)
    (hm : Monotone m) (hlo : ∀ i, B ≤ m i) (hhi : ∀ i, m i ≤ B^3) (L : ℕ) :
    ((range L).filter (fun i => 2*m i < m (i+1))).card ≤ 2*b := by
  let bad := fun i => 2*m i < m (i+1)
  let count := ((range L).filter bad).card
  have hh := paid_steps 2 m hm bad (fun _ h => h.le) L
  have hb : 2^count*B ≤ B^2*B := ((Nat.mul_le_mul_left _ (hlo 0)).trans hh).trans
    ((hhi L).trans_eq (pow_succ B 2))
  have he := (Nat.le_of_mul_le_mul_right hb hB).trans (Nat.pow_le_pow_left hsize 2)
  rw [←pow_mul,Nat.mul_comm b 2] at he
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp he

#print axioms large_step_count
#print axioms doubling_count
end GaloisForLFunctions.HTGeometry.AccuracyScales
