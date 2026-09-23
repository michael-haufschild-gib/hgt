/-
An elementary off-diagonal bound for Dirichlet polynomials with integer frequencies.

The Montgomery–Vaughan off-diagonal `∑_{m≠n} 2|aₘaₙ|/|log(n/m)|` is bounded, for coefficients supported
on `[1, K]`, by `≪ K·log K·∑ aₖ²` — the lower-order companion of the diagonal `U·∑aₖ²` for a long
window.  Unlike the sharp Hilbert-inequality form (which gives `K`), this uses only elementary
estimates and suffices for Carlson's optimization:

* `abs_log_ratio_ge` — `|log n − log m| ≥ |n − m|/K` for `m, n ∈ [1, K]` (from `log x ≥ 1 − 1/x`);
* hence `1/|log(n/m)| ≤ K/|n − m|`, and summing the harmonic `∑_{n≠m} 1/|n−m| ≤ 2·(1 + log K)` with the
  AM–GM symmetrisation `|aₘaₙ| ≤ (aₘ²+aₙ²)/2` gives the `K·log K·∑aₖ²` bound.

This file builds the arithmetic core (`abs_log_ratio_ge`, `inv_abs_log_le`).
-/
import Mathlib

open Real

namespace RHTower

/-- `(n − m)/n ≤ log n − log m` for `m, n ≥ 1` (from `log y ≤ y − 1` at `y = m/n`). -/
theorem sub_div_le_log_sub {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ((n : ℝ) - m) / n ≤ Real.log n - Real.log m := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hkey : Real.log ((m : ℝ) / n) ≤ (m : ℝ) / n - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by positivity)] at hkey
  have hrw : ((n : ℝ) - m) / n = 1 - (m : ℝ) / n := by field_simp
  rw [hrw]; linarith [hkey]

/-- **Log-ratio spacing.**  For distinct `m, n ∈ [1, K]`, `|log n − log m| ≥ |n − m|/K`. -/
theorem abs_log_ratio_ge {m n K : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmK : m ≤ K) (hnK : n ≤ K)
    (hmn : m ≠ n) : (|(n : ℝ) - m|) / (K : ℝ) ≤ |Real.log n - Real.log m| := by
  have hKpos : (0 : ℝ) < K := by
    have : 1 ≤ K := le_trans hm hmK
    exact_mod_cast this
  wlog h : m < n generalizing m n
  · have hnm : n < m := lt_of_le_of_ne (not_lt.mp h) hmn.symm
    rw [abs_sub_comm (n : ℝ) m, abs_sub_comm (Real.log n)]
    exact this hn hm hnK hmK hmn.symm hnm
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hmn' : (m : ℝ) < n := by exact_mod_cast h
    have hnm_pos : (0 : ℝ) < (n : ℝ) - m := by linarith
    have hlog_pos : (0 : ℝ) < Real.log n - Real.log m := by
      have := sub_div_le_log_sub hm hn
      have hnm_div_pos : (0 : ℝ) < ((n : ℝ) - m) / n := by positivity
      linarith
    rw [abs_of_pos hnm_pos, abs_of_pos hlog_pos]
    calc ((n : ℝ) - m) / (K : ℝ) ≤ ((n : ℝ) - m) / n := by
          apply div_le_div_of_nonneg_left hnm_pos.le hnpos
          exact_mod_cast hnK
      _ ≤ Real.log n - Real.log m := sub_div_le_log_sub hm hn

/-- `1/|log(n/m)| ≤ K/|n − m|` for distinct `m, n ∈ [1, K]`. -/
theorem inv_abs_log_le {m n K : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmK : m ≤ K) (hnK : n ≤ K)
    (hmn : m ≠ n) : 1 / |Real.log n - Real.log m| ≤ (K : ℝ) / |(n : ℝ) - m| := by
  have hKpos : (0 : ℝ) < K := by
    have : 1 ≤ K := le_trans hm hmK; exact_mod_cast this
  have hne : (|(n : ℝ) - m|) ≠ 0 := by
    rw [abs_ne_zero, sub_ne_zero]; exact fun hc => hmn (by exact_mod_cast hc.symm)
  have habspos : (0 : ℝ) < |(n : ℝ) - m| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
  calc 1 / |Real.log n - Real.log m|
      ≤ 1 / ((|(n : ℝ) - m|) / (K : ℝ)) :=
        one_div_le_one_div_of_le (div_pos habspos hKpos) (abs_log_ratio_ge hm hn hmK hnK hmn)
    _ = (K : ℝ) / |(n : ℝ) - m| := by rw [one_div_div]

/-- One side of the reciprocal-distance sum: `∑_{n∈t, n<m} 1/(m−n) ≤ ∑_{j≤K} 1/j` when `t ⊆ [1,K]`. -/
theorem sum_inv_dist_lt_le {t : Finset ℕ} {m K : ℕ} (htK : t ⊆ Finset.Icc 1 K) (hmK : m ≤ K)
    (ht : ∀ n ∈ t, n < m) :
    ∑ n ∈ t, 1 / |(n : ℝ) - m| ≤ ∑ j ∈ Finset.Icc 1 K, 1 / (j : ℝ) := by
  have hinj : Set.InjOn (fun n => m - n) ↑t := by
    intro a ha b hb hab
    simp only at hab
    have := ht a (Finset.mem_coe.mp ha); have := ht b (Finset.mem_coe.mp hb); omega
  have hval : ∀ n ∈ t, 1 / |(n : ℝ) - m| = 1 / ((m - n : ℕ) : ℝ) := by
    intro n hn
    have hnm : n < m := ht n hn
    have hlt : (n : ℝ) < m := by exact_mod_cast hnm
    rw [abs_of_neg (by linarith), neg_sub, Nat.cast_sub hnm.le]
  have himg : ∑ j ∈ t.image (fun n => m - n), 1 / (j : ℝ)
      = ∑ n ∈ t, 1 / ((m - n : ℕ) : ℝ) := Finset.sum_image hinj
  rw [Finset.sum_congr rfl hval, ← himg]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨n, hn, hjn⟩ := hj
    have hnm : n < m := ht n hn
    have hnK := htK hn
    rw [Finset.mem_Icc] at hnK ⊢; omega
  · intro j _ _; positivity

/-- One side (`n>m`): `∑_{n∈t, n>m} 1/(n−m) ≤ ∑_{j≤K} 1/j`. -/
theorem sum_inv_dist_gt_le {t : Finset ℕ} {m K : ℕ} (htK : t ⊆ Finset.Icc 1 K)
    (ht : ∀ n ∈ t, m < n) :
    ∑ n ∈ t, 1 / |(n : ℝ) - m| ≤ ∑ j ∈ Finset.Icc 1 K, 1 / (j : ℝ) := by
  have hinj : Set.InjOn (fun n => n - m) ↑t := by
    intro a ha b hb hab
    simp only at hab
    have := ht a (Finset.mem_coe.mp ha); have := ht b (Finset.mem_coe.mp hb); omega
  have hval : ∀ n ∈ t, 1 / |(n : ℝ) - m| = 1 / ((n - m : ℕ) : ℝ) := by
    intro n hn
    have hnm : m < n := ht n hn
    have hlt : (m : ℝ) < n := by exact_mod_cast hnm
    rw [abs_of_pos (by linarith), Nat.cast_sub hnm.le]
  have himg : ∑ j ∈ t.image (fun n => n - m), 1 / (j : ℝ)
      = ∑ n ∈ t, 1 / ((n - m : ℕ) : ℝ) := Finset.sum_image hinj
  rw [Finset.sum_congr rfl hval, ← himg]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨n, hn, hjn⟩ := hj
    have hnm : m < n := ht n hn
    have hnK := htK hn
    rw [Finset.mem_Icc] at hnK ⊢; omega
  · intro j _ _; positivity

/-- **Reciprocal-distance sum bound.**  For `s ⊆ [1,K]`, `∑_{n∈s, n≠m} 1/|n−m| ≤ 2·∑_{j≤K} 1/j`:
splitting `n<m`, `n>m` and reindexing each injectively into `[1,K]`. -/
theorem sum_inv_dist_le {s : Finset ℕ} {m K : ℕ} (hsK : s ⊆ Finset.Icc 1 K) (hmK : m ≤ K) :
    ∑ n ∈ s.erase m, 1 / |(n : ℝ) - m| ≤ 2 * ∑ j ∈ Finset.Icc 1 K, 1 / (j : ℝ) := by
  classical
  have herase : s.erase m ⊆ Finset.Icc 1 K := (Finset.erase_subset _ _).trans hsK
  have hsplit : (s.erase m).filter (fun n => n < m) ∪ (s.erase m).filter (fun n => m < n)
      = s.erase m := by
    ext n
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h; rcases lt_or_gt_of_ne h.1 with hlt | hgt
      · exact Or.inl ⟨h, hlt⟩
      · exact Or.inr ⟨h, hgt⟩
  have hdisj : Disjoint ((s.erase m).filter (fun n => n < m))
      ((s.erase m).filter (fun n => m < n)) := by
    rw [Finset.disjoint_filter]; intro n _ hlt; omega
  rw [← hsplit, Finset.sum_union hdisj, two_mul]
  apply add_le_add
  · exact sum_inv_dist_lt_le ((Finset.filter_subset _ _).trans herase) hmK
      (fun n hn => (Finset.mem_filter.mp hn).2)
  · exact sum_inv_dist_gt_le ((Finset.filter_subset _ _).trans herase)
      (fun n hn => (Finset.mem_filter.mp hn).2)

/-- **The elementary off-diagonal bound.**  For coefficients `e` and support `s ⊆ [1,K]`,
`∑_{m≠n} 2|eₘeₙ|/|log(n/m)| ≤ 4·K·H(K)·∑ₖ eₖ²`, where `H(K) = ∑_{j≤K} 1/j`.  Combines
`inv_abs_log_le` (`1/|log(n/m)| ≤ K/|n−m|`), AM–GM (`2|eₘeₙ| ≤ eₘ²+eₙ²`), and the harmonic
reciprocal-distance sum, with a symmetry swap on the double sum.  This is the lower-order
(`K·log K`) off-diagonal companion of the `U·∑eₖ²` diagonal for a long window. -/
theorem offDiagonal_le {s : Finset ℕ} {K : ℕ} (e : ℕ → ℝ) (hsK : s ⊆ Finset.Icc 1 K) :
    ∑ m ∈ s, ∑ n ∈ s.erase m, 2 * |e m * e n| / |Real.log n - Real.log m|
      ≤ 4 * (K : ℝ) * (∑ j ∈ Finset.Icc 1 K, 1 / (j : ℝ)) * ∑ k ∈ s, (e k) ^ (2 : ℕ) := by
  classical
  -- termwise: 2|eₘeₙ|/|log| ≤ (eₘ²+eₙ²)·K/|n−m|
  have hterm : ∀ m ∈ s, ∀ n ∈ s.erase m,
      2 * |e m * e n| / |Real.log n - Real.log m|
        ≤ ((e m) ^ (2 : ℕ) + (e n) ^ (2 : ℕ)) * ((K : ℝ) / |(n : ℝ) - m|) := by
    intro m hm n hn
    obtain ⟨hnm, hns⟩ := Finset.mem_erase.mp hn
    have hmi := Finset.mem_Icc.mp (hsK hm)
    have hni := Finset.mem_Icc.mp (hsK hns)
    have hinvlog := inv_abs_log_le hmi.1 hni.1 hmi.2 hni.2 (Ne.symm hnm)
    have hamgm : 2 * |e m * e n| ≤ (e m) ^ (2 : ℕ) + (e n) ^ (2 : ℕ) := by
      rw [abs_mul]; nlinarith [sq_nonneg (|e m| - |e n|), abs_nonneg (e m), abs_nonneg (e n),
        sq_abs (e m), sq_abs (e n)]
    have hKdist_nonneg : (0 : ℝ) ≤ (K : ℝ) / |(n : ℝ) - m| := by
      apply div_nonneg (by positivity) (abs_nonneg _)
    calc 2 * |e m * e n| / |Real.log n - Real.log m|
        = 2 * |e m * e n| * (1 / |Real.log n - Real.log m|) := by ring
      _ ≤ ((e m) ^ (2 : ℕ) + (e n) ^ (2 : ℕ)) * ((K : ℝ) / |(n : ℝ) - m|) := by
          apply mul_le_mul hamgm hinvlog (by positivity) (by positivity)
  refine le_trans (Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => hterm m hm n hn) ?_
  -- ∑∑ (eₘ²+eₙ²)·K/|n−m| = K·(A + B), A from eₘ², B from eₙ² (symmetry)
  have hAB : ∑ m ∈ s, ∑ n ∈ s.erase m, ((e m) ^ (2 : ℕ) + (e n) ^ (2 : ℕ)) * ((K : ℝ) / |(n : ℝ) - m|)
      ≤ 4 * (K : ℝ) * (∑ j ∈ Finset.Icc 1 K, 1 / (j : ℝ)) * ∑ k ∈ s, (e k) ^ (2 : ℕ) := by
    have hexpand : ∀ m ∈ s, ∑ n ∈ s.erase m, ((e m) ^ (2 : ℕ) + (e n) ^ (2 : ℕ)) * ((K : ℝ) / |(n : ℝ) - m|)
        = (K : ℝ) * (e m) ^ (2 : ℕ) * (∑ n ∈ s.erase m, 1 / |(n : ℝ) - m|)
          + (K : ℝ) * (∑ n ∈ s.erase m, (e n) ^ (2 : ℕ) / |(n : ℝ) - m|) := by
      intro m _
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro n _
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]; ring
    rw [Finset.sum_congr rfl hexpand, Finset.sum_add_distrib]
    set H : ℝ := ∑ j ∈ Finset.Icc 1 K, 1 / (j : ℝ) with hH
    have hHnn : (0 : ℝ) ≤ H := Finset.sum_nonneg (fun j _ => by positivity)
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
    -- part A: ∑ₘ K·eₘ²·(∑ 1/|n−m|) ≤ 2K·H·∑eₖ²
    have hA : ∑ m ∈ s, (K : ℝ) * (e m) ^ (2 : ℕ) * (∑ n ∈ s.erase m, 1 / |(n : ℝ) - m|)
        ≤ 2 * (K : ℝ) * H * ∑ k ∈ s, (e k) ^ (2 : ℕ) := by
      calc ∑ m ∈ s, (K : ℝ) * (e m) ^ (2 : ℕ) * (∑ n ∈ s.erase m, 1 / |(n : ℝ) - m|)
          ≤ ∑ m ∈ s, (2 * (K : ℝ) * H) * (e m) ^ (2 : ℕ) := by
            apply Finset.sum_le_sum; intro m hm
            have hmK : m ≤ K := (Finset.mem_Icc.mp (hsK hm)).2
            have hd := sum_inv_dist_le hsK hmK
            nlinarith [sq_nonneg (e m), hKnn, hd, hHnn,
              mul_nonneg (mul_nonneg hKnn (sq_nonneg (e m))) (by linarith [hd] : (0:ℝ) ≤ 2 * H - ∑ n ∈ s.erase m, 1 / |(n : ℝ) - m|)]
        _ = 2 * (K : ℝ) * H * ∑ k ∈ s, (e k) ^ (2 : ℕ) := by rw [← Finset.mul_sum]
    -- part B via swap
    have hswap : ∑ m ∈ s, (K : ℝ) * (∑ n ∈ s.erase m, (e n) ^ (2 : ℕ) / |(n : ℝ) - m|)
        = ∑ n ∈ s, (K : ℝ) * (e n) ^ (2 : ℕ) * (∑ m ∈ s.erase n, 1 / |(m : ℝ) - n|) := by
      have hcomm : ∑ m ∈ s, ∑ n ∈ s.erase m, (K : ℝ) * (e n) ^ (2 : ℕ) / |(n : ℝ) - m|
          = ∑ n ∈ s, ∑ m ∈ s.erase n, (K : ℝ) * (e n) ^ (2 : ℕ) / |(n : ℝ) - m| :=
        Finset.sum_comm' (fun m n => by simp only [Finset.mem_erase]; tauto)
      rw [show (∑ m ∈ s, (K : ℝ) * (∑ n ∈ s.erase m, (e n) ^ (2 : ℕ) / |(n : ℝ) - m|))
            = ∑ m ∈ s, ∑ n ∈ s.erase m, (K : ℝ) * (e n) ^ (2 : ℕ) / |(n : ℝ) - m| by
          apply Finset.sum_congr rfl; intro m _; rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro n _; rw [mul_div_assoc], hcomm]
      apply Finset.sum_congr rfl; intro n _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _
      rw [abs_sub_comm, mul_one_div, mul_div_assoc]
    rw [hswap]
    have hB : ∑ n ∈ s, (K : ℝ) * (e n) ^ (2 : ℕ) * (∑ m ∈ s.erase n, 1 / |(m : ℝ) - n|)
        ≤ 2 * (K : ℝ) * H * ∑ k ∈ s, (e k) ^ (2 : ℕ) := by
      calc ∑ n ∈ s, (K : ℝ) * (e n) ^ (2 : ℕ) * (∑ m ∈ s.erase n, 1 / |(m : ℝ) - n|)
          ≤ ∑ n ∈ s, (2 * (K : ℝ) * H) * (e n) ^ (2 : ℕ) := by
            apply Finset.sum_le_sum; intro n hn
            have hnK : n ≤ K := (Finset.mem_Icc.mp (hsK hn)).2
            have hd := sum_inv_dist_le hsK hnK
            nlinarith [sq_nonneg (e n), hKnn, hd, hHnn,
              mul_nonneg (mul_nonneg hKnn (sq_nonneg (e n))) (by linarith [hd] : (0:ℝ) ≤ 2 * H - ∑ m ∈ s.erase n, 1 / |(m : ℝ) - n|)]
        _ = 2 * (K : ℝ) * H * ∑ k ∈ s, (e k) ^ (2 : ℕ) := by rw [← Finset.mul_sum]
    linarith [hA, hB]
  exact hAB

end RHTower
