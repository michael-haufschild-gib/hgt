import Mathlib

/-!
# DQPT: the numerical estimates behind the oracle constructions

Supplementary Notes 3–4 of arXiv:2511.11199 (published Supplementary Notes 4–5) build the
polynomial, logarithm and exponential oracles.  The **gate-count** conclusions of those notes are
resource estimates in an unspecified circuit-cost model and have no determinate formal content;
every genuinely mathematical step inside them is collected here.

Formalised items:
* `dqpt_dyadic_partition_existsUnique` — **(3.6)**: every `n ≥ 3` lies in exactly one dyadic
  block `3·2^{ν−1} ≤ n < 3·2^ν`;
* `dqpt_dyadic_offset_mem` — **(3.7)**: `d = (n − 2^{ν+1})/2^{ν+1} ∈ [−1/4, 1/2)`;
* `dqpt_logb_dyadic` — **(3.8)**: `log₂ n = (ν+1) + log₂(1+d)`;
* `dqpt_log_taylor_remainder` — **(3.10)**: the `log(1+d)` Taylor remainder is at most `2^{-l}`;
* `dqpt_geom_half_sum_le`, `dqpt_geom_pi_quarter_sum_lt` — the geometric rounding bounds
  **(3.11)**, **(4.22)**, **(4.64)**.  Note that **(3.11)** as printed is off by a factor two:
  `η/2·(1 + 1/2 + 1/4 + ⋯) = η`, not `≤ η/2`;
* `dqpt_abs_two_rpow_sub_one_le` — **(4.50)**: `|2^x − 1| ≤ |x|` for `x ≤ 1`;
* `dqpt_two_rpow_series_remainder`, `dqpt_two_rpow_series_remainder_lt` — **(4.54), (4.57)**.
-/

namespace RHTower.DQPT

open Filter Topology Set

noncomputable section

/-! ## The dyadic partition of the logarithm oracle -/

/-- **(3.6).**  Every `n ≥ 3` lies in exactly one block `3·2^{ν−1} ≤ n < 3·2^ν`, `ν ≥ 1`. -/
theorem dqpt_dyadic_partition_existsUnique {n : ℕ} (hn : 3 ≤ n) :
    ∃! ν : ℕ, 1 ≤ ν ∧ 3 * 2 ^ (ν - 1) ≤ n ∧ n < 3 * 2 ^ ν := by
  have hdiv : 1 ≤ n / 3 := (Nat.one_le_div_iff (by norm_num)).mpr hn
  set μ : ℕ := Nat.log 2 (n / 3) with hμ
  have hlow : 2 ^ μ ≤ n / 3 := Nat.pow_log_le_self 2 (by omega)
  have hhigh : n / 3 < 2 ^ (μ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hA : 3 * 2 ^ μ ≤ n := by
    have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).mp hlow
    omega
  have hB : n < 3 * 2 ^ (μ + 1) := by
    have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)).mp hhigh
    omega
  refine ⟨μ + 1, ⟨by omega, by simpa using hA, hB⟩, ?_⟩
  rintro ν ⟨hν1, hν2, hν3⟩
  obtain ⟨a, rfl⟩ : ∃ a, ν = a + 1 := ⟨ν - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hν2
  have hcase : a = μ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hle : (3 : ℕ) * 2 ^ (a + 1) ≤ 3 * 2 ^ μ :=
        Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by norm_num) (by omega))
      omega
    · have hle : (3 : ℕ) * 2 ^ (μ + 1) ≤ 3 * 2 ^ a :=
        Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by norm_num) (by omega))
      omega
  omega

/-- **(3.7).**  The dyadic offset lies in `[−1/4, 1/2)`. -/
theorem dqpt_dyadic_offset_mem {n ν : ℕ} (hν : 1 ≤ ν)
    (h1 : 3 * 2 ^ (ν - 1) ≤ n) (h2 : n < 3 * 2 ^ ν) :
    -(1 / 4 : ℝ) ≤ ((n : ℝ) - 2 ^ (ν + 1)) / 2 ^ (ν + 1)
      ∧ ((n : ℝ) - 2 ^ (ν + 1)) / 2 ^ (ν + 1) < 1 / 2 := by
  obtain ⟨a, rfl⟩ : ∃ a, ν = a + 1 := ⟨ν - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1
  have hpow : (0 : ℝ) < 2 ^ (a + 2) := by positivity
  have hR1 : (3 : ℝ) * 2 ^ a ≤ (n : ℝ) := by exact_mod_cast h1
  have hR2 : (n : ℝ) < 3 * 2 ^ (a + 1) := by exact_mod_cast h2
  have hsplit1 : (2 : ℝ) ^ (a + 2) = 4 * 2 ^ a := by ring
  have hsplit2 : (2 : ℝ) ^ (a + 1) = 2 * 2 ^ a := by ring
  constructor
  · rw [le_div_iff₀ hpow, hsplit1]
    nlinarith [hR1]
  · rw [div_lt_iff₀ hpow, hsplit1]
    nlinarith [hR2, hsplit2]

/-- **(3.8).**  `log₂ n = (ν+1) + log₂(1 + d)` with `d` the dyadic offset. -/
theorem dqpt_logb_dyadic {n ν : ℕ} (hn : 1 ≤ n) :
    Real.logb 2 n
      = ((ν : ℝ) + 1) + Real.logb 2 (1 + ((n : ℝ) - 2 ^ (ν + 1)) / 2 ^ (ν + 1)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpow : (0 : ℝ) < 2 ^ (ν + 1) := by positivity
  have hone : (1 : ℝ) + ((n : ℝ) - 2 ^ (ν + 1)) / 2 ^ (ν + 1) = (n : ℝ) / 2 ^ (ν + 1) := by
    field_simp
    ring
  rw [hone, Real.logb, Real.logb, Real.log_div (ne_of_gt hn0) (ne_of_gt hpow),
    Real.log_pow]
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  push_cast
  ring

/-! ## The Taylor remainder of `log(1+d)` -/

/-- **(3.10).**  For `|d| ≤ 1/2` the `l`-term Taylor remainder of `log(1+d)` is at most `2^{-l}`. -/
theorem dqpt_log_taylor_remainder {d : ℝ} (hd : |d| ≤ 1 / 2) (l : ℕ) :
    |Real.log (1 + d) - ∑ j ∈ Finset.range l, (-1 : ℝ) ^ j * d ^ (j + 1) / (j + 1)|
      ≤ (1 / 2 : ℝ) ^ l := by
  have habs : |(-d)| < 1 := by
    rw [abs_neg]
    linarith [hd]
  have hbase := Real.abs_log_sub_add_sum_range_le habs l
  have hsum : ∑ i ∈ Finset.range l, (-d) ^ (i + 1) / ((i : ℝ) + 1)
      = -∑ j ∈ Finset.range l, (-1 : ℝ) ^ j * d ^ (j + 1) / (j + 1) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [neg_pow]
    field_simp
    ring
  have harg : (1 : ℝ) - (-d) = 1 + d := by ring
  rw [hsum, harg] at hbase
  have hswap : |(-∑ j ∈ Finset.range l, (-1 : ℝ) ^ j * d ^ (j + 1) / (j + 1))
      + Real.log (1 + d)|
      = |Real.log (1 + d) - ∑ j ∈ Finset.range l, (-1 : ℝ) ^ j * d ^ (j + 1) / (j + 1)| := by
    congr 1
    ring
  rw [hswap, abs_neg] at hbase
  refine hbase.trans ?_
  have habs0 : 0 ≤ |d| := abs_nonneg d
  have hden : (1 : ℝ) / 2 ≤ 1 - |d| := by linarith
  have hnum : |d| ^ (l + 1) ≤ (1 / 2 : ℝ) ^ (l + 1) := pow_le_pow_left₀ habs0 hd _
  have hdenpos : (0 : ℝ) < 1 - |d| := by linarith
  calc |d| ^ (l + 1) / (1 - |d|) ≤ (1 / 2 : ℝ) ^ (l + 1) / (1 - |d|) :=
        div_le_div_of_nonneg_right hnum (le_of_lt hdenpos)
    _ ≤ (1 / 2 : ℝ) ^ (l + 1) / (1 / 2) := by
        refine div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = (1 / 2 : ℝ) ^ l := by
        rw [pow_succ]
        field_simp

/-! ## Geometric rounding bounds -/

theorem dqpt_geom_range_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (m : ℕ) :
    ∑ j ∈ Finset.range m, r ^ j ≤ (1 - r)⁻¹ := by
  have hne : r ≠ 1 := ne_of_lt hr1
  have hd : (0 : ℝ) < 1 - r := by linarith
  have heq : ∑ j ∈ Finset.range m, r ^ j = (1 - r ^ m) / (1 - r) := by
    rw [geom_sum_eq hne]
    field_simp
    ring
  rw [heq, inv_eq_one_div]
  have hpow : (0 : ℝ) ≤ r ^ m := pow_nonneg hr0 m
  exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hd)

/-- **(3.11) / (4.64).**  A geometric rounding cascade with ratio `1/2` costs at most `2c`. -/
theorem dqpt_geom_half_sum_le {c : ℝ} (hc : 0 ≤ c) (m : ℕ) :
    ∑ j ∈ Finset.range m, c * (1 / 2 : ℝ) ^ j ≤ 2 * c := by
  rw [← Finset.mul_sum]
  have h := dqpt_geom_range_le (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num) m
  have hval : ((1 : ℝ) - 1 / 2)⁻¹ = 2 := by norm_num
  rw [hval] at h
  nlinarith [h, hc]

/-- **(4.22).**  A geometric rounding cascade with ratio `π/4` costs less than four times the
first term's coefficient. -/
theorem dqpt_geom_pi_quarter_sum_lt (m : ℕ) :
    ∑ j ∈ Finset.range m, (Real.pi / 4) ^ (j + 1) < 4 := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hr0 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have hr1 : Real.pi / 4 < 1 := by linarith
  have hfac : ∑ j ∈ Finset.range m, (Real.pi / 4) ^ (j + 1)
      = (Real.pi / 4) * ∑ j ∈ Finset.range m, (Real.pi / 4) ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [pow_succ]; ring)
  rw [hfac]
  have h := dqpt_geom_range_le hr0 hr1 m
  have hden : (0 : ℝ) < 1 - Real.pi / 4 := by linarith
  have hbound : (Real.pi / 4) * ∑ j ∈ Finset.range m, (Real.pi / 4) ^ j
      ≤ (Real.pi / 4) * (1 - Real.pi / 4)⁻¹ :=
    mul_le_mul_of_nonneg_left h hr0
  refine lt_of_le_of_lt hbound ?_
  rw [mul_inv_lt_iff₀ hden]
  linarith

/-! ## `2^x` near the origin -/

/-- **(4.50).**  `|2^x − 1| ≤ |x|` for every `x ≤ 1`. -/
theorem dqpt_abs_two_rpow_sub_one_le {x : ℝ} (hx : x ≤ 1) : |(2 : ℝ) ^ x - 1| ≤ |x| := by
  have hexp : (2 : ℝ) ^ x = Real.exp (x * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
  have hlog2lt : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases le_total 0 x with hx0 | hx0
  · have hupper : Real.exp (x * Real.log 2) ≤ 1 + x := by
      have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (Real.log 2))
        (by linarith : (0 : ℝ) ≤ 1 - x) hx0 (by ring)
      simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hconv
      calc Real.exp (x * Real.log 2) = Real.exp ((1 - x) * 0 + x * Real.log 2) := by ring_nf
        _ ≤ (1 - x) * 1 + x * 2 := by
            simpa using hconv
        _ = 1 + x := by ring
    have hlower : (1 : ℝ) ≤ Real.exp (x * Real.log 2) := by
      have h1 := Real.add_one_le_exp (x * Real.log 2)
      nlinarith [hx0, hlog2pos]
    rw [hexp, abs_of_nonneg (by linarith), abs_of_nonneg hx0]
    linarith
  · have hlower : (1 : ℝ) + x ≤ Real.exp (x * Real.log 2) := by
      have h1 : x * Real.log 2 + 1 ≤ Real.exp (x * Real.log 2) := by
        simpa [add_comm] using Real.add_one_le_exp (x * Real.log 2)
      nlinarith [h1, hlog2lt, hx0]
    have hupper : Real.exp (x * Real.log 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [hlog2pos, hx0]
    rw [hexp, abs_of_nonpos (by linarith), abs_of_nonpos hx0]
    linarith

/-- **(4.54)–(4.57).**  The degree-`l` truncation error of the series for `2^x` on `|x| ≤ 1/2`. -/
theorem dqpt_two_rpow_series_remainder {x : ℝ} (hx : |x| ≤ 1 / 2) {l : ℕ} (hl : 0 < l) :
    |(2 : ℝ) ^ x - ∑ m ∈ Finset.range l, (Real.log 2 * x) ^ m / m.factorial|
      ≤ 2 * (Real.log 2 / 2) ^ l / l.factorial := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  set y : ℝ := Real.log 2 * x with hy
  have hyabs : |y| ≤ Real.log 2 / 2 := by
    rw [hy, abs_mul, abs_of_pos hlog2pos]
    nlinarith [hx, abs_nonneg x, hlog2pos]
  have hy1 : |y| ≤ 1 := by
    have : Real.log 2 / 2 ≤ 1 := by linarith
    linarith [hyabs]
  have hexp : (2 : ℝ) ^ x = Real.exp y := by
    rw [hy, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hbase := Real.exp_bound hy1 hl
  rw [hexp]
  refine hbase.trans ?_
  have hfac : (0 : ℝ) < (l.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos l
  have hlreal : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hcoef : ((l.succ : ℕ) : ℝ) / ((l.factorial : ℝ) * (l : ℝ)) ≤ 2 / (l.factorial : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hfac]
    push_cast
    nlinarith [hlreal, hfac]
  have hnum : |y| ^ l ≤ (Real.log 2 / 2) ^ l :=
    pow_le_pow_left₀ (abs_nonneg y) hyabs l
  have hnn : (0 : ℝ) ≤ (Real.log 2 / 2) ^ l := by positivity
  calc |y| ^ l * (((l.succ : ℕ) : ℝ) / ((l.factorial : ℝ) * (l : ℝ)))
      ≤ (Real.log 2 / 2) ^ l * (((l.succ : ℕ) : ℝ) / ((l.factorial : ℝ) * (l : ℝ))) := by
        refine mul_le_mul_of_nonneg_right hnum ?_
        positivity
    _ ≤ (Real.log 2 / 2) ^ l * (2 / (l.factorial : ℝ)) := mul_le_mul_of_nonneg_left hcoef hnn
    _ = 2 * (Real.log 2 / 2) ^ l / (l.factorial : ℝ) := by ring

theorem dqpt_four_log_two_pow_lt_factorial {l : ℕ} (hl : 2 ≤ l) :
    4 * Real.log 2 ^ l < (l.factorial : ℝ) := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  induction l, hl using Nat.le_induction with
  | base =>
      have hsq : Real.log 2 ^ 2 < 0.4806 := by nlinarith [hlog2pos, hlog2lt]
      have hf : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
      rw [hf]
      nlinarith [hsq]
  | succ m hm ih =>
      have hfacpos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
      have hmreal : (3 : ℝ) ≤ ((m : ℝ) + 1) := by
        have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
      have hfacsucc : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hpowpos : (0 : ℝ) < Real.log 2 ^ m := by positivity
      rw [hfacsucc, pow_succ]
      nlinarith [ih, hfacpos, hmreal, hlog2pos, hlog2lt, hpowpos]

/-- **(4.57).**  For `l ≥ 2` the truncation error is below `2^{-l-1}`. -/
theorem dqpt_two_rpow_series_remainder_lt {x : ℝ} (hx : |x| ≤ 1 / 2) {l : ℕ} (hl : 2 ≤ l) :
    |(2 : ℝ) ^ x - ∑ m ∈ Finset.range l, (Real.log 2 * x) ^ m / m.factorial|
      < (1 / 2 : ℝ) ^ (l + 1) := by
  have hl0 : 0 < l := by omega
  refine lt_of_le_of_lt (dqpt_two_rpow_series_remainder hx hl0) ?_
  have hfac : (0 : ℝ) < (l.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos l
  have hkey := dqpt_four_log_two_pow_lt_factorial hl
  have hsplit : 2 * (Real.log 2 / 2) ^ l / (l.factorial : ℝ)
      = (1 / 2 : ℝ) ^ (l + 1) * (4 * Real.log 2 ^ l / (l.factorial : ℝ)) := by
    have hp : (Real.log 2 / 2) ^ l = Real.log 2 ^ l * ((1 : ℝ) / 2) ^ l := by
      rw [div_pow, div_pow, one_pow]
      ring
    rw [hp, pow_succ]
    ring
  rw [hsplit]
  have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  have hlt : 4 * Real.log 2 ^ l / (l.factorial : ℝ) < 1 := by
    rw [div_lt_one hfac]
    exact hkey
  nlinarith [hpow, hlt]

end

end RHTower.DQPT
