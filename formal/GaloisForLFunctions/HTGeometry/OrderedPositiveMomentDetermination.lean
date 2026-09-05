import Mathlib

/-!
# Ordered positive moment determinacy

Standard power-sum determinacy, with multiplicity retained by decreasing enumeration.
No claim of scientific novelty.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

theorem summable_pow_succ_of_nonneg_antitone {a : ℕ → ℝ}
    (ha : Summable a) (hpos : ∀ n, 0 ≤ a n) (hanti : Antitone a) (m : ℕ) :
    Summable (fun n => a n ^ (m + 1)) := by
  apply (ha.mul_left (a 0 ^ m)).of_nonneg_of_le
  · intro n; exact pow_nonneg (hpos n) _
  · intro n
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (hpos n) (hanti (Nat.zero_le n)) m) (hpos n)

private theorem orderedMoment_head_le {a b : ℕ → ℝ}
    (ha : Summable a) (hb : Summable b)
    (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n)
    (haa : Antitone a) (hba : Antitone b)
    (hm : ∀ m : ℕ, ∑' n, a n ^ (m + 1) = ∑' n, b n ^ (m + 1)) :
    a 0 ≤ b 0 := by
  by_contra hn
  have hlt : b 0 < a 0 := lt_of_not_ge hn
  have hapos : 0 < a 0 := (hb0 0).trans_lt hlt
  have hgeom : b 0 / a 0 < 1 := (div_lt_one hapos).mpr hlt
  have hlim : Tendsto (fun m : ℕ => (b 0 / a 0) ^ m * ∑' n, b n)
      atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg (hb0 0) hapos.le) hgeom).mul_const (∑' n, b n)
  have hall : ∀ m : ℕ, a 0 ≤ (b 0 / a 0) ^ m * ∑' n, b n := by
    intro m
    have hfirst : a 0 ^ (m + 1) ≤ ∑' n, a n ^ (m + 1) :=
      (summable_pow_succ_of_nonneg_antitone ha ha0 haa m).le_tsum 0
        (fun n _ => pow_nonneg (ha0 n) _)
    have hupper : (∑' n, b n ^ (m + 1)) ≤ b 0 ^ m * ∑' n, b n := by
      rw [← tsum_mul_left]
      apply Summable.tsum_le_tsum _
        (summable_pow_succ_of_nonneg_antitone hb hb0 hba m) (hb.mul_left _)
      intro n
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (hb0 n) (hba (Nat.zero_le n)) m) (hb0 n)
    rw [hm m] at hfirst
    rw [div_pow, div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos hapos m)).mpr
    simpa only [pow_succ, mul_comm] using hfirst.trans hupper
  have hh : a 0 ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hall)
  exact hapos.not_ge hh

/-- All positive power sums determine a decreasing nonnegative summable sequence,
including repeated values and zero tails. This is an ordered moment-determinacy lemma. -/
theorem antitone_nonneg_eq_of_powerSums_eq {a b : ℕ → ℝ}
    (ha : Summable a) (hb : Summable b)
    (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n)
    (haa : Antitone a) (hba : Antitone b)
    (hm : ∀ m : ℕ, ∑' n, a n ^ (m + 1) = ∑' n, b n ^ (m + 1)) :
    a = b := by
  funext k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hat : Summable (fun n => a (n + k)) := (summable_nat_add_iff k).mpr ha
    have hbt : Summable (fun n => b (n + k)) := (summable_nat_add_iff k).mpr hb
    have hma : Antitone (fun n => a (n + k)) := fun _ _ h => haa (Nat.add_le_add_right h k)
    have hmb : Antitone (fun n => b (n + k)) := fun _ _ h => hba (Nat.add_le_add_right h k)
    have ht : ∀ m : ℕ, ∑' n, a (n + k) ^ (m + 1) = ∑' n, b (n + k) ^ (m + 1) := by
      intro m
      have hsa := (summable_pow_succ_of_nonneg_antitone ha ha0 haa m).sum_add_tsum_nat_add k
      have hsb := (summable_pow_succ_of_nonneg_antitone hb hb0 hba m).sum_add_tsum_nat_add k
      have hh : (∑ n ∈ Finset.range k, a n ^ (m + 1)) =
          ∑ n ∈ Finset.range k, b n ^ (m + 1) := by
        exact Finset.sum_congr rfl (fun n hn => by rw [ih n (Finset.mem_range.mp hn)])
      rw [hh, hm m] at hsa
      linarith
    have hab := orderedMoment_head_le hat hbt (fun n => ha0 _) (fun n => hb0 _) hma hmb ht
    have hba' := orderedMoment_head_le hbt hat (fun n => hb0 _) (fun n => ha0 _) hmb hma
      (fun m => (ht m).symm)
    simpa using le_antisymm hab hba'

end GaloisForLFunctions.HTGeometry
