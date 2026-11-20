import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Variation under a decreasing envelope

The long and short increments in a variation sum can be split at a
drop of the amplitude envelope. Across a drop, the envelope pays by
telescoping. Between drops, weighted nearest-neighbor variation pays.
The resulting estimate is uniform over all sampling grids.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

private theorem increment_le_fine (f : ℕ → ℝ) {a b : ℕ} (h : a≤b) :
    |f b-f a| ≤ ∑ j ∈ Ico a b, |f (j+1)-f j| := by
  induction b,h using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [sum_Ico_succ_top hb]
    calc |f (b+1)-f a| ≤ |f b-f a| + |f (b+1)-f b| := by
           rw [show f (b+1)-f a = (f b-f a)+(f (b+1)-f b) by ring]
           exact abs_add_le _ _
         _ ≤ _ := add_le_add ih le_rfl

/-- A single increment pays either from loss of envelope or from
nearest-neighbor movement weighted by the envelope at the later site. -/
theorem envelope_variation_interval (f u : ℕ → ℝ) (hu : Antitone u)
    (hf : ∀ n, |f n|≤u n) {q : ℝ} (hq : 1≤q) {a b : ℕ} (hab : a≤b) :
    |f b-f a|^q ≤ 2*(2:ℝ)^q*(u a^q-u b^q) +
      (4:ℝ)^(q-1)*∑ j ∈ Ico a b, u (j+1)^(q-1)*|f (j+1)-f j| := by
  have hpos (n : ℕ) : 0≤u n := (abs_nonneg _).trans (hf n)
  have hq₀ : 0≤q := zero_le_one.trans hq
  have hq₁ : 0≤q-1 := sub_nonneg.mpr hq
  have bound : |f b-f a| ≤ 2*u a := by
    have ht := abs_add_le (f b) (-(f a))
    rw [abs_neg,←sub_eq_add_neg] at ht
    have h := ht.trans (add_le_add (hf b) (hf a))
    linarith only [h,hu hab]
  have drop : 0 ≤ u a^q-u b^q := sub_nonneg.mpr (Real.rpow_le_rpow (hpos b) (hu hab) hq₀)
  have hfine : 0 ≤ ∑ j ∈ Ico a b, u (j+1)^(q-1)*|f (j+1)-f j| :=
    sum_nonneg fun j _ => mul_nonneg (Real.rpow_nonneg (hpos _) _) (abs_nonneg _)
  by_cases hd : 2*u b ≤ u a
  · have hpow := Real.rpow_le_rpow (mul_nonneg (by norm_num) (hpos b)) hd hq₀
    rw [Real.mul_rpow (by norm_num) (hpos b)] at hpow
    have two_le : (2:ℝ)≤2^q := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hq
    have hpay : u a^q ≤ 2*(u a^q-u b^q) := by
      linarith only [(mul_le_mul_of_nonneg_right two_le (Real.rpow_nonneg (hpos b) q)).trans hpow]
    have h := Real.rpow_le_rpow (abs_nonneg _) bound hq₀
    rw [Real.mul_rpow (by norm_num) (hpos a)] at h
    apply h.trans
    have h' := mul_le_mul_of_nonneg_left hpay (Real.rpow_nonneg (by norm_num : 0≤(2:ℝ)) q)
    linarith only [h',mul_nonneg (Real.rpow_nonneg (by norm_num : 0≤(4:ℝ)) (q-1)) hfine]
  · have he : |f b-f a|^q = |f b-f a|^(q-1)*|f b-f a| := by
      by_cases hz : |f b-f a|=0
      · rw [hz,Real.zero_rpow (lt_of_lt_of_le zero_lt_one hq).ne',mul_zero]
      · have h' := Real.rpow_add (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz)) (q-1) 1
        simpa only [sub_add_cancel,Real.rpow_one] using h'
    rw [he]
    apply le_trans (mul_le_mul_of_nonneg_left (increment_le_fine f hab) (Real.rpow_nonneg (abs_nonneg _) _))
    refine le_trans ?_ (le_add_of_nonneg_left (mul_nonneg (by positivity) drop))
    rw [mul_sum,mul_sum]
    apply sum_le_sum
    intro j hj
    rw [←mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    rw [←Real.mul_rpow (by norm_num) (hpos (j+1))]
    apply Real.rpow_le_rpow (abs_nonneg _) _ hq₁
    have h := hu (show j+1≤b from (mem_Ico.mp hj).2)
    linarith only [bound,h,lt_of_not_ge hd]

/-- The variation on an arbitrary monotone sampling grid is controlled
by one telescoping endpoint term and one weighted fine-grid sum. -/
theorem envelope_variation_grid (f u : ℕ → ℝ) (hu : Antitone u) (hf : ∀ n, |f n|≤u n)
    {q : ℝ} (hq : 1≤q) (t : ℕ → ℕ) (ht : Monotone t) (M : ℕ) :
    ∑ i ∈ range M, |f (t (i+1))-f (t i)|^q ≤
      2*(2:ℝ)^q*(u (t 0)^q-u (t M)^q) +
      (4:ℝ)^(q-1)*∑ j ∈ Ico (t 0) (t M), u (j+1)^(q-1)*|f (j+1)-f j| := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hstep := envelope_variation_interval f u hu hf hq (ht (Nat.le_succ M))
    rw [sum_range_succ]
    apply (add_le_add ih hstep).trans_eq
    have hjoin := sum_Ico_consecutive (fun j => u (j+1)^(q-1)*|f (j+1)-f j|)
      (ht (Nat.zero_le M)) (ht (Nat.le_succ M))
    rw [←hjoin]
    ring

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
