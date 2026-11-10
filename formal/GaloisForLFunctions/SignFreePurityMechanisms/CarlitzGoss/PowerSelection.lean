import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitValues
import Mathlib.Data.Finset.Max

/-!
# Selecting an exact power from a digit subcollection

If powers of one base all divide a target and their total reaches it, a
subcollection sums to the target exactly. Remove a largest power and apply
induction to the remainder; every remaining power still divides that remainder.

Each cyclic weighted content is a sum of rotated residue powers. The selection
lemma therefore extracts a digit subcollection attaining any such power once
the weighted total reaches it and all individual weights are bounded by it.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

/-- Powers of one base dividing a target can realize it exactly once their total reaches it. -/
theorem exists_subset_pow_sum_eq {α : Type*} [DecidableEq α] (p : ℕ)
    (exponent : α → ℕ) (S : Finset α) :
    ∀ N : ℕ, (∀ x ∈ S, p ^ exponent x ∣ N) → N ≤ ∑ x ∈ S, p ^ exponent x →
      ∃ T ⊆ S, (∑ x ∈ T, p ^ exponent x) = N := by
  refine Finset.strongInductionOn S ?_
  intro S ih N hdiv hsum
  by_cases hN : N = 0
  · exact ⟨∅, empty_subset S, by simp only [sum_empty, hN]⟩
  have hS : S.Nonempty := by
    by_contra hn
    have he : S = ∅ := not_nonempty_iff_eq_empty.mp hn
    simp only [he, sum_empty, Nat.le_zero] at hsum
    exact hN hsum
  obtain ⟨x, hx, hmax⟩ := S.exists_max_image exponent hS
  have hxN : p ^ exponent x ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (hdiv x hx)
  have hrest : ∀ y ∈ S.erase x, p ^ exponent y ∣ N - p ^ exponent x := by
    intro y hy
    have hyS := (mem_erase.mp hy).2
    obtain ⟨a, ha⟩ := hdiv y hyS
    obtain ⟨b, hb⟩ := pow_dvd_pow p (hmax y hyS)
    exact ⟨a - b, by rw [ha, hb, Nat.mul_sub_left_distrib]⟩
  have hsumrest : N - p ^ exponent x ≤ ∑ y ∈ S.erase x, p ^ exponent y := by
    have he := sum_erase_add S (fun y => p ^ exponent y) hx
    omega
  obtain ⟨T, hT, heT⟩ := ih (S.erase x) (erase_ssubset hx) (N - p ^ exponent x) hrest hsumrest
  have hxT : x ∉ T := fun hh => (mem_erase.mp (hT hh)).1 rfl
  refine ⟨insert x T, insert_subset hx (hT.trans (erase_subset _ _)), ?_⟩
  rw [sum_insert hxT, heT, Nat.add_sub_of_le hxN]

/-- A collection of powers bounded by p^k contains a subcollection summing to p^k
as soon as its total reaches that value. -/
theorem exists_subset_sum_eq_pow {α : Type*} [DecidableEq α] (p : ℕ)
    (exponent : α → ℕ) (S : Finset α) (k : ℕ)
    (hbound : ∀ x ∈ S, exponent x ≤ k) (hsum : p ^ k ≤ ∑ x ∈ S, p ^ exponent x) :
    ∃ T ⊆ S, (∑ x ∈ T, p ^ exponent x) = p ^ k :=
  exists_subset_pow_sum_eq p exponent S (p ^ k)
    (fun x hx => pow_dvd_pow p (hbound x hx)) hsum

/-- Every cyclic row counts digit occurrences with their rotated exponent weights. -/
theorem cyclicWeighted_tokenContent_at {s : ℕ} [NeZero s] {α : Type*}
    (p : ℕ) (colour : α → ZMod s) (S : Finset α) (h : ZMod s) :
    cyclicWeighted (p : ℤ) (tokenContent colour S) h =
      ∑ x ∈ S, (p : ℤ) ^ (colour x - h).val := by
  unfold cyclicWeighted tokenContent
  simp only [card_filter, Nat.cast_sum, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_eq_single (colour x - h).val]
  · rw [ZMod.natCast_zmod_val, show h + (colour x - h) = colour x by ring]
    simp only [ite_true, Nat.cast_one, mul_one]
  · intro k hk hk0
    have hne : colour x ≠ h + (k : ZMod s) := by
      intro he
      have he' : colour x - h = (k : ZMod s) := by rw [he]; ring
      have hh := congrArg ZMod.val he'
      rw [ZMod.val_natCast_of_lt (mem_range.mp hk)] at hh
      exact hk0 hh.symm
    simp only [if_neg hne, Nat.cast_zero, mul_zero]
  · intro hnot
    exact (hnot (mem_range.mpr (ZMod.val_lt _))).elim

/-- A cyclic weighted content crossing a power contains a subcontent attaining it exactly. -/
theorem exists_subset_cyclicWeighted_eq_pow {s : ℕ} [NeZero s] {α : Type*} [DecidableEq α]
    (p : ℕ) (colour : α → ZMod s) (S : Finset α) (h : ZMod s) (k : ℕ)
    (hbound : ∀ x ∈ S, (colour x - h).val ≤ k)
    (hsum : (p : ℤ) ^ k ≤ cyclicWeighted (p : ℤ) (tokenContent colour S) h) :
    ∃ T ⊆ S, cyclicWeighted (p : ℤ) (tokenContent colour T) h = (p : ℤ) ^ k := by
  rw [cyclicWeighted_tokenContent_at] at hsum
  have hn : p ^ k ≤ ∑ x ∈ S, p ^ (colour x - h).val := by exact_mod_cast hsum
  obtain ⟨T, hT, he⟩ := exists_subset_sum_eq_pow p (fun x => (colour x - h).val) S k hbound hn
  refine ⟨T, hT, ?_⟩
  rw [cyclicWeighted_tokenContent_at]
  exact_mod_cast he

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.exists_subset_sum_eq_pow
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.exists_subset_cyclicWeighted_eq_pow
