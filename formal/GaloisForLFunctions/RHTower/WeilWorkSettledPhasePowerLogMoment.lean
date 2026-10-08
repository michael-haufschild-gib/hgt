import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Power growth from a logarithmic moment ceiling

The discrete logarithmic moment argument works for every real ratio above one.
Its exact exponent will be used for complex powers of a Weil source.
-/

open Finset

noncomputable section
namespace RHTower.WeilWorkSettledPhase

private theorem rpow_tangent {x d p : ℝ} (hx : 0 < x) (hd : 0 ≤ d)
    (hp : 1 ≤ p) : x ^ p + p * x ^ (p - 1) * d ≤ (x + d) ^ p := by
  have h := one_add_mul_self_le_rpow_one_add
    (s := d / x) (le_trans (by norm_num : (-1 : ℝ) ≤ 0) (div_nonneg hd hx.le)) hp
  have hm := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hx.le p)
  have he : x ^ p * (1 + d / x) ^ p = (x + d) ^ p := by
    rw [← Real.mul_rpow hx.le (by positivity)]
    congr 1
    field_simp
  rw [he] at hm
  rw [Real.rpow_sub_one hx.ne']
  calc
    _ = x ^ p * (1 + p * (d / x)) := by ring
    _ ≤ _ := hm

/-- A normalized logarithmic moment ceiling gives its exact power exponent. -/
theorem sum_le_log_rpow_of_normalized_moment {w : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n) {c α : ℝ} (hc : 0 ≤ c) (hα : 1 < α)
    (hbound : ∀ N : ℕ, 1 ≤ N →
      (Real.log N - c) * ∑ n ∈ Icc 1 N, w n ≤
        α * (Real.log N * ∑ n ∈ Icc 1 N, w n -
          ∑ n ∈ Icc 1 N, Real.log n * w n)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ Icc 1 N, w n ≤ K * (1 + Real.log N) ^ (α - 1) := by
  let E (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, w n
  let S (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, Real.log n * w n
  let H (N : ℕ) : ℝ := Real.log N * E N - S N
  have hE0 (N : ℕ) : 0 ≤ E N := sum_nonneg fun n _ => hw n
  have hEmono {M N : ℕ} (h : M ≤ N) : E M ≤ E N := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans h⟩
    · intro n _ _
      exact hw n
  have hH0 (N : ℕ) : 0 ≤ H N := by
    dsimp [H, E, S]
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_nonneg
    intro n hn
    have hn' := mem_Icc.mp hn
    have hl : Real.log n ≤ Real.log N := Real.log_le_log
      (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast hn'.2)
    nlinarith [hw n]
  have hmoment (N : ℕ) (hN : 1 ≤ N) :
      (Real.log N - c) * E N ≤ α * H N := hbound N hN
  have hrec (N : ℕ) (hN : 1 ≤ N) :
      H (N + 1) = H N + (Real.log (N + 1) - Real.log N) * E N := by
    have he : E (N + 1) = E N + w (N + 1) := sum_Icc_succ_top (by omega) w
    have hs : S (N + 1) = S N + Real.log (N + 1) * w (N + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        sum_Icc_succ_top (by omega : 1 ≤ N + 1) (fun n => Real.log n * w n)
    simp only [H, he, hs, Nat.cast_add, Nat.cast_one]
    ring
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (Real.exp (c + 1))
  have hN₀pos : 0 < N₀ := by
    exact_mod_cast (Real.exp_pos (c + 1)).trans hN₀
  have hd₀ : 0 < Real.log N₀ - c := by
    have h := Real.log_lt_log (Real.exp_pos (c + 1)) hN₀
    rw [Real.log_exp] at h
    linarith
  let K₀ := H N₀ / (Real.log N₀ - c) ^ α
  have hK₀ : 0 ≤ K₀ := div_nonneg (hH0 N₀) (Real.rpow_nonneg hd₀.le α)
  have hd {N : ℕ} (hN : N₀ ≤ N) : 0 < Real.log N - c := by
    have h := Real.log_le_log (x := (N₀ : ℝ)) (y := (N : ℝ))
      (by exact_mod_cast hN₀pos) (by exact_mod_cast hN)
    linarith
  have henergy {N : ℕ} (hN : N₀ ≤ N)
      (hh : H N ≤ K₀ * (Real.log N - c) ^ α) :
      E N ≤ α * K₀ * (Real.log N - c) ^ (α - 1) := by
    apply le_of_mul_le_mul_left (a := Real.log N - c) _ (hd hN)
    calc
      (Real.log N - c) * E N ≤ α * H N := hmoment N (hN₀pos.trans_le hN)
      _ ≤ α * (K₀ * (Real.log N - c) ^ α) :=
        mul_le_mul_of_nonneg_left hh (by linarith)
      _ = (Real.log N - c) * (α * K₀ * (Real.log N - c) ^ (α - 1)) := by
        rw [Real.rpow_sub_one (hd hN).ne']
        field_simp [(hd hN).ne']
  have hlarge : ∀ N : ℕ, N₀ ≤ N → H N ≤ K₀ * (Real.log N - c) ^ α := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      dsimp [K₀]
      rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hd₀ α).ne']
    | succ N hN ih =>
      have hN1 : 1 ≤ N := hN₀pos.trans_le hN
      have hdelta : 0 ≤ Real.log (N + 1) - Real.log N := sub_nonneg.mpr
        (Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) (by linarith))
      have he := mul_le_mul_of_nonneg_left (henergy hN ih) hdelta
      have ht := mul_le_mul_of_nonneg_left
        (rpow_tangent (hd hN) hdelta hα.le) hK₀
      have hadd : Real.log N - c + (Real.log (N + 1) - Real.log N) =
          Real.log (N + 1) - c := by ring
      rw [hadd] at ht
      rw [hrec N hN1]
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith
  refine ⟨E N₀ + α * K₀, add_nonneg (hE0 N₀) (mul_nonneg (by linarith) hK₀),
    fun N hN => ?_⟩
  change E N ≤ (E N₀ + α * K₀) * (1 + Real.log N) ^ (α - 1)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hp : 1 ≤ (1 + Real.log N) ^ (α - 1) :=
    Real.one_le_rpow (by linarith) (by linarith)
  rcases le_total N₀ N with h | h
  · have hb := henergy h (hlarge N h)
    have hr := Real.rpow_le_rpow (hd h).le
      (show Real.log N - c ≤ 1 + Real.log N by linarith) (show 0 ≤ α - 1 by linarith)
    have hm := mul_le_mul_of_nonneg_left hr (mul_nonneg (by linarith : 0 ≤ α) hK₀)
    have he := mul_nonneg (hE0 N₀) (show 0 ≤ (1 + Real.log N) ^ (α - 1) by linarith)
    nlinarith
  · have hb := hEmono h
    have he := mul_le_mul_of_nonneg_left hp (hE0 N₀)
    have hk := mul_nonneg (mul_nonneg (by linarith : 0 ≤ α) hK₀)
      (show 0 ≤ (1 + Real.log N) ^ (α - 1) by linarith)
    nlinarith

/-- A logarithmic moment ratio `r > 1` forces growth exponent `1 / (r - 1)`. -/
theorem sum_le_log_rpow_of_log_moment {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    {C r : ℝ} (hC : 0 ≤ C) (hr : 1 < r)
    (hbound : ∀ N : ℕ, 1 ≤ N →
      r * ∑ n ∈ Icc 1 N, Real.log n * w n ≤
        (Real.log N + C) * ∑ n ∈ Icc 1 N, w n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ Icc 1 N, w n ≤ K * (1 + Real.log N) ^ (1 / (r - 1)) := by
  have hr0 : 0 < r - 1 := by linarith
  have hα : 1 < r / (r - 1) := (lt_div_iff₀ hr0).mpr (by linarith)
  have he : r / (r - 1) - 1 = 1 / (r - 1) := by field_simp; ring
  have h := sum_le_log_rpow_of_normalized_moment hw (div_nonneg hC hr0.le) hα
    (fun N hN => ?_)
  · simpa only [he] using h
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hr0).mpr
    have hb := hbound N hN
    have hc : (Real.log N - C / (r - 1)) * (∑ n ∈ Icc 1 N, w n) * (r - 1) =
        ((r - 1) * Real.log N - C) * (∑ n ∈ Icc 1 N, w n) := by
      field_simp [hr0.ne']
    rw [hc]
    nlinarith

end RHTower.WeilWorkSettledPhase
