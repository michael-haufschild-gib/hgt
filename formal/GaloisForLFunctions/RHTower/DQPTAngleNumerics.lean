import Mathlib

/-!
# DQPT: the angle-oracle numerics

Supplementary Note 4 of arXiv:2511.11199 (published Supplementary Note 5), equations
(4.18)–(4.20), estimates the bisection oracle for the amplitude-splitting angles:

* the power series `sin²θ = ∑_{n≥1} (−1)^{n+1} 2^{2n} θ^{2n} / (2(2n)!)` and its truncation
  error **(4.19)–(4.20)**;
* the separation `sin²(θ+δ) − sin²(θ) > δ²/2` used to distinguish two trial angles **(4.18)**.

Main results:
* `dqpt_cos_taylor_remainder` — `|cos y − ∑_{k<K} (−1)^k y^{2k}/(2k)!| ≤ |y|^{2K}/(2K)!`;
* `dqpt_sin_sq_taylor_remainder` — **(4.19)–(4.20)**;
* `dqpt_sin_sq_separation` — **(4.18)**.
-/

namespace RHTower.DQPT

open Filter Topology Set

noncomputable section

/-! ## The cosine Taylor remainder -/

theorem dqpt_summable_cos_terms (y : ℝ) :
    Summable (fun n : ℕ => y ^ (2 * n) / ((2 * n).factorial : ℝ)) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (Real.summable_pow_div_factorial (y ^ 2))
  have hfac : (n.factorial : ℝ) ≤ ((2 * n).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hfacpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hnum : y ^ (2 * n) = (y ^ 2) ^ n := by
    rw [← pow_mul, Nat.mul_comm]
  rw [hnum]
  refine div_le_div_of_nonneg_left (by positivity) hfacpos hfac

theorem dqpt_antitone_cos_terms {y : ℝ} (hy : |y| ≤ 1) :
    Antitone (fun n : ℕ => y ^ (2 * n) / ((2 * n).factorial : ℝ)) := by
  refine antitone_nat_of_succ_le (fun n => ?_)
  have hy2 : y ^ 2 ≤ 1 := by
    have := abs_nonneg y
    nlinarith [sq_abs y, hy]
  have hfacpos : (0 : ℝ) < ((2 * n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hfacpos' : (0 : ℝ) < ((2 * (n + 1)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hstep : ((2 * (n + 1)).factorial : ℝ)
      = ((2 * n + 2 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) * ((2 * n).factorial : ℝ)) := by
    have h1 : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
    rw [h1, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hpowstep : y ^ (2 * (n + 1)) = y ^ (2 * n) * y ^ 2 := by
    rw [← pow_add]
    congr 1
    ring
  simp only
  rw [hpowstep, hstep, div_le_div_iff₀ (by positivity) hfacpos]
  have hnn : (0 : ℝ) ≤ y ^ (2 * n) := by
    have : y ^ (2 * n) = (y ^ 2) ^ n := by rw [← pow_mul, Nat.mul_comm]
    rw [this]; positivity
  have hc1 : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ 2 * n + 1 := by omega
    exact_mod_cast this
  have hc2 : (2 : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) := by
    have : (2 : ℕ) ≤ 2 * n + 2 := by omega
    exact_mod_cast this
  nlinarith [hnn, hy2, hfacpos, hc1, hc2]

/-- The cosine Taylor remainder after `K` terms. -/
theorem dqpt_cos_taylor_remainder {y : ℝ} (hy : |y| ≤ 1) (K : ℕ) :
    |Real.cos y - ∑ k ∈ Finset.range K, (-1 : ℝ) ^ k * y ^ (2 * k) / ((2 * k).factorial : ℝ)|
      ≤ y ^ (2 * K) / ((2 * K).factorial : ℝ) := by
  have hbase := alternating_series_error_bound
    (fun n : ℕ => y ^ (2 * n) / ((2 * n).factorial : ℝ))
    (dqpt_antitone_cos_terms hy) (dqpt_summable_cos_terms y) K
  have hcos : Real.cos y
      = ∑' n : ℕ, (-1 : ℝ) ^ n * (y ^ (2 * n) / ((2 * n).factorial : ℝ)) := by
    rw [Real.cos_eq_tsum]
    exact tsum_congr (fun n => by ring)
  rw [← hcos] at hbase
  refine le_of_eq_of_le ?_ hbase
  congr 2
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-! ## Supplementary Note 4 (4.19)–(4.20) -/

/-- **(4.19)–(4.20).**  The truncation error of the `sin²` power series. -/
theorem dqpt_sin_sq_taylor_remainder {θ : ℝ} (hθ : |2 * θ| ≤ 1) (l : ℕ) :
    |Real.sin θ ^ 2 - ∑ n ∈ Finset.range l,
        (-1 : ℝ) ^ n * 2 ^ (2 * (n + 1)) * θ ^ (2 * (n + 1))
          / (2 * ((2 * (n + 1)).factorial : ℝ))|
      ≤ (2 * θ) ^ (2 * (l + 1)) / (2 * ((2 * (l + 1)).factorial : ℝ)) := by
  have hsin : Real.sin θ ^ 2 = (1 - Real.cos (2 * θ)) / 2 := by
    have h := Real.cos_two_mul' θ
    have hpy := Real.sin_sq_add_cos_sq θ
    linarith [h, hpy]
  have hbase := dqpt_cos_taylor_remainder hθ (l + 1)
  have hsplit : ∑ k ∈ Finset.range (l + 1),
        (-1 : ℝ) ^ k * (2 * θ) ^ (2 * k) / ((2 * k).factorial : ℝ)
      = 1 + ∑ n ∈ Finset.range l,
          (-1 : ℝ) ^ (n + 1) * (2 * θ) ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ) := by
    rw [Finset.sum_range_succ']
    simp
  have hmid : (1 - ∑ k ∈ Finset.range (l + 1),
        (-1 : ℝ) ^ k * (2 * θ) ^ (2 * k) / ((2 * k).factorial : ℝ)) / 2
      = ∑ n ∈ Finset.range l,
          (-1 : ℝ) ^ n * 2 ^ (2 * (n + 1)) * θ ^ (2 * (n + 1))
            / (2 * ((2 * (n + 1)).factorial : ℝ)) := by
    rw [hsplit]
    rw [show (1 : ℝ) - (1 + ∑ n ∈ Finset.range l,
        (-1 : ℝ) ^ (n + 1) * (2 * θ) ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ))
        = -∑ n ∈ Finset.range l,
          (-1 : ℝ) ^ (n + 1) * (2 * θ) ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ) by ring]
    rw [neg_div, ← Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_div]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    have hmul : (2 * θ) ^ (2 * (n + 1)) = 2 ^ (2 * (n + 1)) * θ ^ (2 * (n + 1)) := by
      rw [mul_pow]
    have hfacpos : (0 : ℝ) < ((2 * (n + 1)).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    rw [hmul, pow_succ]
    field_simp
    ring
  have hkey : Real.sin θ ^ 2 - ∑ n ∈ Finset.range l,
        (-1 : ℝ) ^ n * 2 ^ (2 * (n + 1)) * θ ^ (2 * (n + 1))
          / (2 * ((2 * (n + 1)).factorial : ℝ))
      = -(Real.cos (2 * θ)
          - ∑ k ∈ Finset.range (l + 1),
            (-1 : ℝ) ^ k * (2 * θ) ^ (2 * k) / ((2 * k).factorial : ℝ)) / 2 := by
    rw [hsin, ← hmid]
    ring
  rw [hkey, abs_div, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  have hfacpos : (0 : ℝ) < ((2 * (l + 1)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hnn : (0 : ℝ) ≤ (2 * θ) ^ (2 * (l + 1)) := by
    have hrw : (2 * θ) ^ (2 * (l + 1)) = ((2 * θ) ^ 2) ^ (l + 1) := by
      rw [← pow_mul, Nat.mul_comm]
    rw [hrw]; positivity
  nlinarith [hbase, hfacpos, hnn]

/-! ## Supplementary Note 4 (4.18): the angle separation -/

/-- **(4.18).**  Two trial angles separated by `δ` inside `[0, π/4]` give `sin²` values separated
by more than `δ²/2`. -/
theorem dqpt_sin_sq_separation {θ δ : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ) (hsum : θ + δ ≤ Real.pi / 4) :
    δ ^ 2 / 2 < Real.sin (θ + δ) ^ 2 - Real.sin θ ^ 2 := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hδle : δ ≤ Real.pi / 4 := by linarith
  have hδsmall : δ ≤ 0.7875 := by linarith
  have hhalf : 2 * θ + δ ≤ Real.pi / 2 := by linarith
  have hid : Real.sin (θ + δ) ^ 2 - Real.sin θ ^ 2
      = Real.sin (2 * θ + δ) * Real.sin δ := by
    have h1 : Real.sin (θ + δ) ^ 2 = (1 - Real.cos (2 * (θ + δ))) / 2 := by
      have h := Real.cos_two_mul' (θ + δ)
      have hpy := Real.sin_sq_add_cos_sq (θ + δ)
      linarith [h, hpy]
    have h2 : Real.sin θ ^ 2 = (1 - Real.cos (2 * θ)) / 2 := by
      have h := Real.cos_two_mul' θ
      have hpy := Real.sin_sq_add_cos_sq θ
      linarith [h, hpy]
    have h3 := Real.cos_sub_cos (2 * θ) (2 * (θ + δ))
    have harg1 : (2 * θ + 2 * (θ + δ)) / 2 = 2 * θ + δ := by ring
    have harg2 : (2 * θ - 2 * (θ + δ)) / 2 = -δ := by ring
    rw [harg1, harg2, Real.sin_neg] at h3
    rw [h1, h2]
    linarith [h3]
  have hsinδpos : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith)
  have hmono : Real.sin δ ≤ Real.sin (2 * θ + δ) := by
    rcases eq_or_lt_of_le (show δ ≤ 2 * θ + δ by linarith) with h | h
    · rw [h]
    · exact le_of_lt (Real.strictMonoOn_sin ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩ h)
  have hcube : δ - δ ^ 3 / 6 < Real.sin δ := Real.sin_gt_sub_cube hδ
  have hlin : 0.87 * δ ≤ δ - δ ^ 3 / 6 := by nlinarith [hδ, hδsmall]
  have hlow : 0.87 * δ < Real.sin δ := lt_of_le_of_lt hlin hcube
  rw [hid]
  nlinarith [hmono, hlow, hsinδpos, hδ]

end

end RHTower.DQPT
