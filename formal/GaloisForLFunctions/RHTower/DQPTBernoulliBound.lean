import Mathlib

/-!
# DQPT: the Bernoulli-number bounds of the Euler–Maclaurin oracle

Supplementary Note 4 of arXiv:2511.11199 (published Supplementary Note 5), Corollary 4.6 and
equations (4.33)/(4.39):

* `B₀ = 1` and `∑_{p=0}^{q} C(q+1, p) B_p = 0` for `q ≥ 1`;
* `|B_{2l}| = 2(2l)!·ζ(2l)/(2π)^{2l}` and
  `2(2l)!/(2π)^{2l}·(1 − 2^{−2l})^{-1} ≤ |B_{2l}| ≤ 2(2l)!/(2π)^{2l}·(1 − 2^{1−2l})^{-1}`.

Main results:
* `dqpt_bernoulli_recurrence` — Corollary 4.6;
* `dqpt_zeta_even_lower`, `dqpt_zeta_even_upper` — `(1−2^{−2k})^{-1} ≤ ζ(2k) ≤ (1−2^{1−2k})^{-1}`;
* `dqpt_abs_bernoulli_eq`, `dqpt_abs_bernoulli_bounds` — **(4.33)**.
-/

namespace RHTower.DQPT

open Filter Topology Set

noncomputable section

/-! ## Corollary 4.6: the Bernoulli recurrence -/

theorem dqpt_bernoulli_zero : bernoulli 0 = 1 := bernoulli_zero

/-- **Corollary 4.6.**  `∑_{p=0}^{q} C(q+1, p)·B_p = 0` for every `q ≥ 1`. -/
theorem dqpt_bernoulli_recurrence {q : ℕ} (hq : 1 ≤ q) :
    ∑ p ∈ Finset.range (q + 1), ((q + 1).choose p : ℚ) * bernoulli p = 0 := by
  have h := sum_bernoulli (q + 1)
  rw [if_neg (by omega : ¬ (q + 1 = 1))] at h
  exact h

/-! ## The even zeta values -/

/-- `ζ(2k) = ∑_{n≥1} n^{−2k}`, written as a sum over all of `ℕ` (the `n = 0` term vanishes). -/
def dqptZetaEven (k : ℕ) : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k)

theorem dqpt_summable_zetaEven {k : ℕ} (hk : k ≠ 0) :
    Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 * k)) :=
  Real.summable_one_div_nat_pow.mpr (by omega)

theorem dqpt_summable_odd {k : ℕ} (hk : k ≠ 0) :
    Summable (fun m : ℕ => 1 / ((2 * m + 1 : ℕ) : ℝ) ^ (2 * k)) :=
  (dqpt_summable_zetaEven hk).comp_injective (fun a b hab => by omega)

theorem dqpt_summable_evenIdx {k : ℕ} (hk : k ≠ 0) :
    Summable (fun m : ℕ => 1 / ((2 * m : ℕ) : ℝ) ^ (2 * k)) :=
  (dqpt_summable_zetaEven hk).comp_injective (fun a b hab => by omega)

theorem dqpt_summable_shift {k : ℕ} (hk : k ≠ 0) :
    Summable (fun m : ℕ => 1 / ((2 * m + 2 : ℕ) : ℝ) ^ (2 * k)) :=
  (dqpt_summable_zetaEven hk).comp_injective (fun a b hab => by omega)

/-- The even-index part is `2^{−2k}` times the whole sum. -/
theorem dqpt_evenIdx_eq {k : ℕ} (hk : k ≠ 0) :
    ∑' m : ℕ, 1 / ((2 * m : ℕ) : ℝ) ^ (2 * k)
      = (1 / (2 : ℝ) ^ (2 * k)) * dqptZetaEven k := by
  rw [dqptZetaEven, ← (dqpt_summable_zetaEven hk).tsum_mul_left]
  refine tsum_congr (fun m => ?_)
  have hcast : (((2 * m : ℕ)) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  rw [hcast, mul_pow]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
    ring
  · have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    field_simp

/-- The even/odd decomposition of `ζ(2k)`. -/
theorem dqpt_zetaEven_split {k : ℕ} (hk : k ≠ 0) :
    dqptZetaEven k
      = (1 / (2 : ℝ) ^ (2 * k)) * dqptZetaEven k
        + ∑' m : ℕ, 1 / ((2 * m + 1 : ℕ) : ℝ) ^ (2 * k) := by
  have hsplit := tsum_even_add_odd (f := fun n : ℕ => 1 / (n : ℝ) ^ (2 * k))
    (dqpt_summable_evenIdx hk) (dqpt_summable_odd hk)
  rw [dqpt_evenIdx_eq hk] at hsplit
  exact hsplit.symm

theorem dqpt_four_le_two_pow {k : ℕ} (hk : k ≠ 0) : (4 : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by
  have h2 : (2 : ℝ) ^ (2 : ℕ) ≤ (2 : ℝ) ^ (2 * k) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at h2
  linarith

theorem dqpt_two_pow_lt_one {k : ℕ} (hk : k ≠ 0) : (1 : ℝ) / (2 : ℝ) ^ (2 * k) ≤ 1 / 4 := by
  have h4 := dqpt_four_le_two_pow hk
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

theorem dqpt_one_le_zetaEven {k : ℕ} (hk : k ≠ 0) : 1 ≤ dqptZetaEven k := by
  have hterm : ∀ n : ℕ, (0 : ℝ) ≤ 1 / (n : ℝ) ^ (2 * k) := fun n => by positivity
  have hfirst := (dqpt_summable_zetaEven hk).le_tsum 1 (fun n _ => hterm n)
  simpa [dqptZetaEven] using hfirst

/-- **Lower bound.**  `(1 − 2^{−2k})^{-1} ≤ ζ(2k)`. -/
theorem dqpt_zeta_even_lower {k : ℕ} (hk : k ≠ 0) :
    ((1 : ℝ) - 1 / (2 : ℝ) ^ (2 * k))⁻¹ ≤ dqptZetaEven k := by
  have hsmall := dqpt_two_pow_lt_one hk
  have hden : (0 : ℝ) < 1 - 1 / (2 : ℝ) ^ (2 * k) := by linarith
  have hsplit := dqpt_zetaEven_split hk
  have hO : (1 : ℝ) ≤ ∑' m : ℕ, 1 / ((2 * m + 1 : ℕ) : ℝ) ^ (2 * k) := by
    have hterm : ∀ m : ℕ, (0 : ℝ) ≤ 1 / ((2 * m + 1 : ℕ) : ℝ) ^ (2 * k) := by
      intro m; positivity
    have hfirst := (dqpt_summable_odd hk).le_tsum 0 (fun m _ => hterm m)
    simpa using hfirst
  have hO' : (1 : ℝ) ≤ (1 - 1 / (2 : ℝ) ^ (2 * k)) * dqptZetaEven k := by
    have hkey : (1 - 1 / (2 : ℝ) ^ (2 * k)) * dqptZetaEven k
        = ∑' m : ℕ, 1 / ((2 * m + 1 : ℕ) : ℝ) ^ (2 * k) := by
      linear_combination hsplit
    rw [hkey]; exact hO
  calc ((1 : ℝ) - 1 / (2 : ℝ) ^ (2 * k))⁻¹
      = 1 / (1 - 1 / (2 : ℝ) ^ (2 * k)) := inv_eq_one_div _
    _ ≤ ((1 - 1 / (2 : ℝ) ^ (2 * k)) * dqptZetaEven k) / (1 - 1 / (2 : ℝ) ^ (2 * k)) :=
        div_le_div_of_nonneg_right hO' (le_of_lt hden)
    _ = dqptZetaEven k := by
        rw [mul_comm, mul_div_assoc, div_self (ne_of_gt hden), mul_one]

/-- The strengthened partial-sum bound for the alternating even-zeta series. -/
theorem dqpt_alt_partial_strong (k : ℕ) (K : ℕ) :
    ∑ i ∈ Finset.range K,
        (1 / ((2 * i + 1 : ℕ) : ℝ) ^ (2 * k) - 1 / ((2 * i + 2 : ℕ) : ℝ) ^ (2 * k))
      + 1 / ((2 * K + 1 : ℕ) : ℝ) ^ (2 * k) ≤ 1 := by
  induction K with
  | zero => norm_num
  | succ K ih =>
      rw [Finset.sum_range_succ]
      have hmono : (1 : ℝ) / ((2 * (K + 1) + 1 : ℕ) : ℝ) ^ (2 * k)
          ≤ 1 / ((2 * K + 2 : ℕ) : ℝ) ^ (2 * k) := by
        have hb : ((2 * K + 2 : ℕ) : ℝ) ≤ ((2 * (K + 1) + 1 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : (2 * K + 2 : ℕ) ≤ 2 * (K + 1) + 1)
        have hp : (0 : ℝ) < ((2 * K + 2 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : 0 < 2 * K + 2)
        have hp2 : (0 : ℝ) < ((2 * K + 2 : ℕ) : ℝ) ^ (2 * k) := by positivity
        exact one_div_le_one_div_of_le hp2 (pow_le_pow_left₀ (le_of_lt hp) hb (2 * k))
      linarith [ih, hmono]

/-- **Upper bound.**  `ζ(2k) ≤ (1 − 2^{1−2k})^{-1}`. -/
theorem dqpt_zeta_even_upper {k : ℕ} (hk : k ≠ 0) :
    dqptZetaEven k ≤ ((1 : ℝ) - 2 / (2 : ℝ) ^ (2 * k))⁻¹ := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (2 * k) := by positivity
  have h4 := dqpt_four_le_two_pow hk
  have hden : (0 : ℝ) < 1 - 2 / (2 : ℝ) ^ (2 * k) := by
    rw [sub_pos, div_lt_one hp]
    linarith
  have hshift : ∑' m : ℕ, 1 / ((2 * m : ℕ) : ℝ) ^ (2 * k)
      = ∑' m : ℕ, 1 / ((2 * m + 2 : ℕ) : ℝ) ^ (2 * k) := by
    rw [(dqpt_summable_evenIdx hk).tsum_eq_zero_add]
    have hzero : (1 : ℝ) / ((2 * 0 : ℕ) : ℝ) ^ (2 * k) = 0 := by
      norm_num
      exact hk
    rw [hzero, zero_add]
    refine tsum_congr (fun m => ?_)
    congr 3
  have halt : ∑' m : ℕ, (1 / ((2 * m + 1 : ℕ) : ℝ) ^ (2 * k)
        - 1 / ((2 * m + 2 : ℕ) : ℝ) ^ (2 * k))
      = (1 - 2 / (2 : ℝ) ^ (2 * k)) * dqptZetaEven k := by
    rw [(dqpt_summable_odd hk).tsum_sub (dqpt_summable_shift hk), ← hshift, dqpt_evenIdx_eq hk]
    have h := dqpt_zetaEven_split hk
    linear_combination -h
  have hbound : ∑' m : ℕ, (1 / ((2 * m + 1 : ℕ) : ℝ) ^ (2 * k)
      - 1 / ((2 * m + 2 : ℕ) : ℝ) ^ (2 * k)) ≤ 1 := by
    refine Real.tsum_le_of_sum_range_le (fun m => ?_) (fun K => ?_)
    · have hb : ((2 * m + 1 : ℕ) : ℝ) ≤ ((2 * m + 2 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : (2 * m + 1 : ℕ) ≤ 2 * m + 2)
      have hq : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < 2 * m + 1)
      have hq2 : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) ^ (2 * k) := by positivity
      have hle := one_div_le_one_div_of_le hq2 (pow_le_pow_left₀ (le_of_lt hq) hb (2 * k))
      linarith
    · have hstrong := dqpt_alt_partial_strong k K
      have hnn : (0 : ℝ) ≤ 1 / ((2 * K + 1 : ℕ) : ℝ) ^ (2 * k) := by positivity
      linarith
  rw [halt] at hbound
  calc dqptZetaEven k
      = ((1 - 2 / (2 : ℝ) ^ (2 * k)) * dqptZetaEven k) / (1 - 2 / (2 : ℝ) ^ (2 * k)) := by
        rw [mul_comm, mul_div_assoc, div_self (ne_of_gt hden), mul_one]
    _ ≤ 1 / (1 - 2 / (2 : ℝ) ^ (2 * k)) :=
        div_le_div_of_nonneg_right hbound (le_of_lt hden)
    _ = ((1 : ℝ) - 2 / (2 : ℝ) ^ (2 * k))⁻¹ := (inv_eq_one_div _).symm

/-! ## Supplementary Note 4 (4.33): the Bernoulli-number bounds -/

theorem dqpt_zetaEven_eq_bernoulli {k : ℕ} (hk : k ≠ 0) :
    dqptZetaEven k
      = (-1 : ℝ) ^ (k + 1) * 2 ^ (2 * k - 1) * Real.pi ^ (2 * k)
          * ((bernoulli (2 * k) : ℚ) : ℝ) / ((2 * k).factorial : ℝ) :=
  (hasSum_zeta_nat hk).tsum_eq

/-- **(4.33), the exact identity.**  `|B_{2k}| = 2(2k)!·ζ(2k)/(2π)^{2k}`. -/
theorem dqpt_abs_bernoulli_eq {k : ℕ} (hk : k ≠ 0) :
    |((bernoulli (2 * k) : ℚ) : ℝ)|
      = 2 * ((2 * k).factorial : ℝ) * dqptZetaEven k / (2 * Real.pi) ^ (2 * k) := by
  have hF : (0 : ℝ) < ((2 * k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hT : (0 : ℝ) < (2 : ℝ) ^ (2 * k - 1) := by positivity
  have hP : (0 : ℝ) < Real.pi ^ (2 * k) := by positivity
  have hZ1 := dqpt_one_le_zetaEven hk
  have hZ := dqpt_zetaEven_eq_bernoulli hk
  have hkey : (-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℚ) : ℝ)
      * ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k))
      = dqptZetaEven k * ((2 * k).factorial : ℝ) := by
    rw [hZ]
    field_simp
  have hpos : 0 < (-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℚ) : ℝ) := by
    have h1 : 0 < dqptZetaEven k * ((2 * k).factorial : ℝ) := by nlinarith [hZ1, hF]
    nlinarith [hkey, h1, mul_pos hT hP]
  have hs : |((-1 : ℝ) ^ (k + 1))| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  have habs : |((bernoulli (2 * k) : ℚ) : ℝ)|
      = (-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℚ) : ℝ) := by
    calc |((bernoulli (2 * k) : ℚ) : ℝ)|
        = |((-1 : ℝ) ^ (k + 1))| * |((bernoulli (2 * k) : ℚ) : ℝ)| := by rw [hs, one_mul]
      _ = |(-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℚ) : ℝ)| := (abs_mul _ _).symm
      _ = (-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℚ) : ℝ) := abs_of_pos hpos
  have hpow2 : (2 * Real.pi) ^ (2 * k) = 2 ^ (2 * k) * Real.pi ^ (2 * k) := mul_pow _ _ _
  have hsplit : (2 : ℝ) ^ (2 * k) = 2 * (2 : ℝ) ^ (2 * k - 1) := by
    conv_lhs => rw [show 2 * k = (2 * k - 1) + 1 from by omega]
    rw [pow_succ]
    ring
  rw [habs, hpow2, hsplit]
  field_simp
  linarith [hkey]

/-- **(4.33).**  The two-sided Bernoulli bound. -/
theorem dqpt_abs_bernoulli_bounds {k : ℕ} (hk : k ≠ 0) :
    2 * ((2 * k).factorial : ℝ) / (2 * Real.pi) ^ (2 * k)
          * ((1 : ℝ) - 1 / (2 : ℝ) ^ (2 * k))⁻¹
        ≤ |((bernoulli (2 * k) : ℚ) : ℝ)|
      ∧ |((bernoulli (2 * k) : ℚ) : ℝ)|
        ≤ 2 * ((2 * k).factorial : ℝ) / (2 * Real.pi) ^ (2 * k)
            * ((1 : ℝ) - 2 / (2 : ℝ) ^ (2 * k))⁻¹ := by
  have hF : (0 : ℝ) < ((2 * k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ (2 * k) := by positivity
  have hc : (0 : ℝ) < 2 * ((2 * k).factorial : ℝ) / (2 * Real.pi) ^ (2 * k) := by positivity
  have heq := dqpt_abs_bernoulli_eq hk
  have hlow := dqpt_zeta_even_lower hk
  have hupp := dqpt_zeta_even_upper hk
  have hform : 2 * ((2 * k).factorial : ℝ) * dqptZetaEven k / (2 * Real.pi) ^ (2 * k)
      = (2 * ((2 * k).factorial : ℝ) / (2 * Real.pi) ^ (2 * k)) * dqptZetaEven k := by
    field_simp
  rw [heq, hform]
  exact ⟨mul_le_mul_of_nonneg_left hlow (le_of_lt hc),
    mul_le_mul_of_nonneg_left hupp (le_of_lt hc)⟩

end

end RHTower.DQPT
