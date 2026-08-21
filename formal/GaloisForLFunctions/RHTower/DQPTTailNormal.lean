import GaloisForLFunctions.RHTower.DQPTAltPartialSum

/-!
# DQPT: the sharp normal of the alternating tail

Supplementary Note 1 of arXiv:2511.11199 (published Supplementary Note 1) proves

`¼ (N+1)^{−β} ≤ |R_N(s)| ≤ ¾ (N+1)^{−β}`  for all large `N`,   `s = β + it`, `β > 0`,

by writing `R_N` as a Gamma integral and splitting `1/(1+e^{−τ}) = ½ + ½ tanh(τ/2)`.
The paper's threshold is non-effective: it depends on an auxiliary parameter `A = A(s)` chosen so
that an incomplete Gamma tail is at most `|Γ(s)|/4`.

Here the same conclusion is obtained by an equivalent, sharper and fully elementary argument.
Write `g(k) = (N+1+k)^{−s}` and `A_N = ∑_{j≥0} (g(2j) − g(2j+1))`, so that `R_N = (−1)^N A_N`.
Then

* `A_N + A_{N+1} = g(0)`   (telescoping, `dqptAltTail_add_succ`),
* `A_N − A_{N+1} = ∑_{j≥0} (g(2j) − 2g(2j+1) + g(2j+2))`,

whence `A_N = ½ g(0) + ½ D_N` with `D_N` the second-difference series.  The second-difference bound
`‖g(k) − 2g(k+1) + g(k+2)‖ ≤ ‖s‖‖s+1‖(N+1+k)^{−β−2}` and the elementary estimate
`∑_{j≥0} (M+2j)^{−2} ≤ 3/(2M)` give

`‖A_N − ½(N+1)^{−s}‖ ≤ ¾‖s‖‖s+1‖(N+1)^{−β−1}`,

which yields the paper's two-sided bound with the **explicit** threshold `N + 1 ≥ 3‖s‖‖s+1‖`.

Main results:
* `dqptAltTail_eq_half_add_secondDiff` — `2 A_N = (N+1)^{−s} + D_N`;
* `dqptAltTail_sub_half_norm_le` — `‖A_N − ½(N+1)^{−s}‖ ≤ ¾‖s‖‖s+1‖(N+1)^{−β−1}`;
* `dqptAltTail_norm_lower`, `dqptAltTail_norm_upper` — **Supplementary Note 1 (1.17)**.
-/

namespace RHTower.DQPT

open Complex Filter Topology Set

noncomputable section

/-! ## Two `rpow` splittings -/

theorem dqpt_rpow_sub_two {x : ℝ} (hx : 0 < x) (b : ℝ) :
    x ^ (-b - 2) = x ^ (-b) * ((1 : ℝ) / x ^ 2) := by
  rw [show (-b - 2 : ℝ) = -b + (-2 : ℝ) by ring, Real.rpow_add hx]
  congr 1
  rw [Real.rpow_neg hx.le]
  norm_num

theorem dqpt_rpow_sub_one {x : ℝ} (hx : 0 < x) (b : ℝ) :
    x ^ (-b - 1) = x ^ (-b) * x⁻¹ := by
  rw [show (-b - 1 : ℝ) = -b + (-1 : ℝ) by ring, Real.rpow_add hx, Real.rpow_neg_one]

/-! ## An elementary shifted inverse-square tail bound -/

/-- Every partial sum of `∑_{j} (M+2j)^{−2}` is at most `3/(2M)` when `M ≥ 1`. -/
theorem dqpt_sum_range_inv_sq_shift_le {M : ℝ} (hM : 1 ≤ M) (n : ℕ) :
    ∑ j ∈ Finset.range n, (1 : ℝ) / (M + 2 * j) ^ 2 ≤ 3 / (2 * M) := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hwpos : ∀ j : ℕ, (0 : ℝ) < M + 2 * (j : ℝ) := fun j => by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j; linarith
  have hstep : ∀ j : ℕ, (1 : ℝ) / (M + 2 * ((j + 1 : ℕ) : ℝ)) ^ 2
      ≤ ((1 : ℝ) / (M + 2 * (j : ℝ)) - (1 : ℝ) / (M + 2 * ((j + 1 : ℕ) : ℝ))) / 2 := by
    intro j
    have h1 : (0 : ℝ) < M + 2 * (j : ℝ) := hwpos j
    have h2 : (0 : ℝ) < M + 2 * ((j + 1 : ℕ) : ℝ) := hwpos (j + 1)
    have hle : M + 2 * (j : ℝ) ≤ M + 2 * ((j + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hprod : ((1 : ℝ) / (M + 2 * (j : ℝ)) - (1 : ℝ) / (M + 2 * ((j + 1 : ℕ) : ℝ))) / 2
        = (1 : ℝ) / ((M + 2 * (j : ℝ)) * (M + 2 * ((j + 1 : ℕ) : ℝ))) := by
      have hc : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
      rw [hc] at h2 ⊢
      field_simp
      ring
    rw [hprod]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  cases n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; positivity
  | succ m =>
      rw [Finset.sum_range_succ']
      have hhead : ∑ j ∈ Finset.range m, (1 : ℝ) / (M + 2 * ((j + 1 : ℕ) : ℝ)) ^ 2
          ≤ ∑ j ∈ Finset.range m,
              ((1 : ℝ) / (M + 2 * (j : ℝ)) - (1 : ℝ) / (M + 2 * ((j + 1 : ℕ) : ℝ))) / 2 :=
        Finset.sum_le_sum (fun j _ => hstep j)
      have htel : ∑ j ∈ Finset.range m,
            ((1 : ℝ) / (M + 2 * (j : ℝ)) - (1 : ℝ) / (M + 2 * ((j + 1 : ℕ) : ℝ))) / 2
          = ((1 : ℝ) / (M + 2 * ((0 : ℕ) : ℝ))
              - (1 : ℝ) / (M + 2 * ((m : ℕ) : ℝ))) / 2 := by
        rw [← Finset.sum_div]
        congr 1
        exact Finset.sum_range_sub' (fun j : ℕ => (1 : ℝ) / (M + 2 * (j : ℝ))) m
      have hwm : (0 : ℝ) ≤ (1 : ℝ) / (M + 2 * ((m : ℕ) : ℝ)) := le_of_lt (by
        have := hwpos m; positivity)
      have hzero : (M + 2 * ((0 : ℕ) : ℝ)) = M := by norm_num
      have htail : ∑ j ∈ Finset.range m, (1 : ℝ) / (M + 2 * ((j + 1 : ℕ) : ℝ)) ^ 2
          ≤ 1 / (2 * M) := by
        refine hhead.trans ?_
        rw [htel, hzero]
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by positivity)]
        have : (1 : ℝ) / M * (2 * M) = 2 := by field_simp
        nlinarith [hwm]
      have hbase : (1 : ℝ) / (M + 2 * ((0 : ℕ) : ℝ)) ^ 2 ≤ 1 / M := by
        rw [hzero, div_le_div_iff₀ (by positivity) hM0]
        nlinarith
      have hfin : (1 : ℝ) / (2 * M) + 1 / M = 3 / (2 * M) := by field_simp; ring
      calc ∑ j ∈ Finset.range m, (1 : ℝ) / (M + 2 * ((j + 1 : ℕ) : ℝ)) ^ 2
            + (1 : ℝ) / (M + 2 * ((0 : ℕ) : ℝ)) ^ 2
          ≤ 1 / (2 * M) + 1 / M := add_le_add htail hbase
        _ = 3 / (2 * M) := hfin

theorem dqpt_summable_inv_sq_shift {M : ℝ} (hM : 1 ≤ M) :
    Summable (fun j : ℕ => (1 : ℝ) / (M + 2 * j) ^ 2) :=
  summable_of_sum_range_le (fun j => by positivity) (dqpt_sum_range_inv_sq_shift_le hM)

theorem dqpt_tsum_inv_sq_shift_le {M : ℝ} (hM : 1 ≤ M) :
    ∑' j : ℕ, (1 : ℝ) / (M + 2 * j) ^ 2 ≤ 3 / (2 * M) :=
  Real.tsum_le_of_sum_range_le (fun j => by positivity) (dqpt_sum_range_inv_sq_shift_le hM)

/-! ## The second-difference series -/

/-- The `j`-th second difference `g(2j) − 2g(2j+1) + g(2j+2)` of the tail. -/
def dqptTailSecondDiff (s : ℂ) (N : ℕ) (j : ℕ) : ℂ :=
  dqptRp s ((N : ℝ) + 1 + 2 * j) - 2 * dqptRp s ((N : ℝ) + 1 + 2 * j + 1)
    + dqptRp s ((N : ℝ) + 1 + 2 * j + 2)

theorem dqptAltTailTerm_sub_succ (s : ℂ) (N j : ℕ) :
    dqptAltTailTerm s N j - dqptAltTailTerm s (N + 1) j = dqptTailSecondDiff s N j := by
  rw [dqptAltTailTerm, dqptAltTailTerm, dqptTailSecondDiff]
  have e1 : (((N + 1 : ℕ) : ℝ) + 1 + 2 * j) = ((N : ℝ) + 1 + 2 * j + 1) := by push_cast; ring
  have e2 : (((N + 1 : ℕ) : ℝ) + 2 + 2 * j) = ((N : ℝ) + 1 + 2 * j + 2) := by push_cast; ring
  have e3 : ((N : ℝ) + 2 + 2 * j) = ((N : ℝ) + 1 + 2 * j + 1) := by ring
  rw [e1, e2, e3]
  ring

/-- The second-difference bound, term by term. -/
theorem norm_dqptTailSecondDiff_le {s : ℂ} (hs : 0 < s.re) (N j : ℕ) :
    ‖dqptTailSecondDiff s N j‖
      ≤ ‖s‖ * ‖s + 1‖ * ((N : ℝ) + 1 + 2 * j) ^ (-s.re - 2) := by
  have ha : (0 : ℝ) < (N : ℝ) + 1 + 2 * j := by positivity
  exact dqptRp_second_diff_norm_le hs ha

/-- The comparison majorant for the second-difference series. -/
theorem norm_dqptTailSecondDiff_le_majorant {s : ℂ} (hs : 0 < s.re) (N j : ℕ) :
    ‖dqptTailSecondDiff s N j‖
      ≤ ‖s‖ * ‖s + 1‖ * ((N : ℝ) + 1) ^ (-s.re)
        * ((1 : ℝ) / ((N : ℝ) + 1 + 2 * j) ^ 2) := by
  have hM0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have ha : (0 : ℝ) < (N : ℝ) + 1 + 2 * j := by positivity
  refine (norm_dqptTailSecondDiff_le hs N j).trans ?_
  rw [dqpt_rpow_sub_two ha s.re]
  have hmono : ((N : ℝ) + 1 + 2 * j) ^ (-s.re) ≤ ((N : ℝ) + 1) ^ (-s.re) := by
    refine Real.rpow_le_rpow_of_nonpos hM0 ?_ (by linarith)
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hpos : (0 : ℝ) ≤ (1 : ℝ) / ((N : ℝ) + 1 + 2 * j) ^ 2 := by positivity
  calc ‖s‖ * ‖s + 1‖
          * (((N : ℝ) + 1 + 2 * j) ^ (-s.re) * ((1 : ℝ) / ((N : ℝ) + 1 + 2 * j) ^ 2))
      ≤ ‖s‖ * ‖s + 1‖
          * (((N : ℝ) + 1) ^ (-s.re) * ((1 : ℝ) / ((N : ℝ) + 1 + 2 * j) ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmono hpos) (by positivity)
    _ = ‖s‖ * ‖s + 1‖ * ((N : ℝ) + 1) ^ (-s.re)
          * ((1 : ℝ) / ((N : ℝ) + 1 + 2 * j) ^ 2) := by ring

theorem summable_dqptTailSecondDiff {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Summable (dqptTailSecondDiff s N) := by
  refine ((summable_dqptAltTailTerm hs N).sub (summable_dqptAltTailTerm hs (N + 1))).congr ?_
  intro j; exact dqptAltTailTerm_sub_succ s N j

theorem dqptAltTail_sub_succ {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    dqptAltTail s N - dqptAltTail s (N + 1) = ∑' j : ℕ, dqptTailSecondDiff s N j := by
  rw [dqptAltTail, dqptAltTail,
    ← (summable_dqptAltTailTerm hs N).tsum_sub (summable_dqptAltTailTerm hs (N + 1))]
  exact tsum_congr fun j => dqptAltTailTerm_sub_succ s N j

/-- **`2 A_N = (N+1)^{−s} + D_N`.**  Adding the telescoping law to the second-difference law. -/
theorem dqptAltTail_eq_half_add_secondDiff {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    2 * dqptAltTail s N
      = dqptRp s ((N : ℝ) + 1) + ∑' j : ℕ, dqptTailSecondDiff s N j := by
  have hadd := dqptAltTail_add_succ hs N
  have hsub := dqptAltTail_sub_succ hs N
  linear_combination hadd + hsub

/-- **The tail normal.**  `‖A_N − ½(N+1)^{−s}‖ ≤ ¾‖s‖‖s+1‖(N+1)^{−β−1}`. -/
theorem dqptAltTail_sub_half_norm_le {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖dqptAltTail s N - (1 / 2 : ℂ) * dqptRp s ((N : ℝ) + 1)‖
      ≤ 3 / 4 * (‖s‖ * ‖s + 1‖) * ((N : ℝ) + 1) ^ (-s.re - 1) := by
  have hM0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hM : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N; linarith
  have hMne : ((N : ℝ) + 1) ≠ 0 := ne_of_gt hM0
  set K : ℝ := ‖s‖ * ‖s + 1‖ * ((N : ℝ) + 1) ^ (-s.re) with hK
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  have hmaj : Summable (fun j : ℕ => K * ((1 : ℝ) / (((N : ℝ) + 1) + 2 * j) ^ 2)) :=
    (dqpt_summable_inv_sq_shift hM).mul_left K
  have hbnd : ∀ j : ℕ, ‖dqptTailSecondDiff s N j‖
      ≤ K * ((1 : ℝ) / (((N : ℝ) + 1) + 2 * j) ^ 2) := by
    intro j
    rw [hK]
    exact norm_dqptTailSecondDiff_le_majorant hs N j
  have hnorm : ‖∑' j : ℕ, dqptTailSecondDiff s N j‖
      ≤ ∑' j : ℕ, K * ((1 : ℝ) / (((N : ℝ) + 1) + 2 * j) ^ 2) :=
    tsum_of_norm_bounded hmaj.hasSum hbnd
  have hmajval : ∑' j : ℕ, K * ((1 : ℝ) / (((N : ℝ) + 1) + 2 * j) ^ 2)
      ≤ K * (3 / (2 * ((N : ℝ) + 1))) := by
    rw [(dqpt_summable_inv_sq_shift hM).tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (dqpt_tsum_inv_sq_shift_le hM) hKnn
  have hhalf : dqptAltTail s N - (1 / 2 : ℂ) * dqptRp s ((N : ℝ) + 1)
      = (1 / 2 : ℂ) * ∑' j : ℕ, dqptTailSecondDiff s N j := by
    have h := dqptAltTail_eq_half_add_secondDiff hs N
    linear_combination h / 2
  have hchain : ‖∑' j : ℕ, dqptTailSecondDiff s N j‖ ≤ K * (3 / (2 * ((N : ℝ) + 1))) :=
    hnorm.trans hmajval
  have hfinal : (1 / 2 : ℝ) * (K * (3 / (2 * ((N : ℝ) + 1))))
      = 3 / 4 * (‖s‖ * ‖s + 1‖) * ((N : ℝ) + 1) ^ (-s.re - 1) := by
    rw [hK, dqpt_rpow_sub_one hM0 s.re]
    field_simp
    ring
  rw [hhalf, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  calc (1 / 2 : ℝ) * ‖∑' j : ℕ, dqptTailSecondDiff s N j‖
      ≤ (1 / 2 : ℝ) * (K * (3 / (2 * ((N : ℝ) + 1)))) :=
        mul_le_mul_of_nonneg_left hchain (by norm_num)
    _ = 3 / 4 * (‖s‖ * ‖s + 1‖) * ((N : ℝ) + 1) ^ (-s.re - 1) := hfinal

/-! ## Supplementary Note 1, equation (1.17) -/

theorem dqpt_threshold_bound {s : ℂ} {N : ℕ}
    (hN : 3 * (‖s‖ * ‖s + 1‖) ≤ (N : ℝ) + 1) :
    3 / 4 * (‖s‖ * ‖s + 1‖) * ((N : ℝ) + 1) ^ (-s.re - 1)
      ≤ 1 / 4 * ((N : ℝ) + 1) ^ (-s.re) := by
  have hM0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [dqpt_rpow_sub_one hM0 s.re]
  have hpow : (0 : ℝ) < ((N : ℝ) + 1) ^ (-s.re) := Real.rpow_pos_of_pos hM0 _
  rw [show 3 / 4 * (‖s‖ * ‖s + 1‖) * (((N : ℝ) + 1) ^ (-s.re) * ((N : ℝ) + 1)⁻¹)
      = (((N : ℝ) + 1) ^ (-s.re)) * (3 / 4 * (‖s‖ * ‖s + 1‖) * ((N : ℝ) + 1)⁻¹) by ring,
    show 1 / 4 * ((N : ℝ) + 1) ^ (-s.re) = (((N : ℝ) + 1) ^ (-s.re)) * (1 / 4) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hpow)
  rw [mul_inv_le_iff₀ hM0]
  linarith

/-- **Supplementary Note 1 (1.17), lower half.**  `¼(N+1)^{−β} ≤ ‖A_N(s)‖`. -/
theorem dqptAltTail_norm_lower {s : ℂ} (hs : 0 < s.re) {N : ℕ}
    (hN : 3 * (‖s‖ * ‖s + 1‖) ≤ (N : ℝ) + 1) :
    1 / 4 * ((N : ℝ) + 1) ^ (-s.re) ≤ ‖dqptAltTail s N‖ := by
  have hM0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hd := (dqptAltTail_sub_half_norm_le hs N).trans (dqpt_threshold_bound hN)
  have hgn : ‖(1 / 2 : ℂ) * dqptRp s ((N : ℝ) + 1)‖ = 1 / 2 * ((N : ℝ) + 1) ^ (-s.re) := by
    rw [norm_mul, dqptRp_norm hM0]
    norm_num
  have h2 : ‖(1 / 2 : ℂ) * dqptRp s ((N : ℝ) + 1)‖ - ‖dqptAltTail s N‖
      ≤ ‖(1 / 2 : ℂ) * dqptRp s ((N : ℝ) + 1) - dqptAltTail s N‖ := norm_sub_norm_le _ _
  rw [norm_sub_rev, hgn] at h2
  linarith

/-- **Supplementary Note 1 (1.17), upper half.**  `‖A_N(s)‖ ≤ ¾(N+1)^{−β}`. -/
theorem dqptAltTail_norm_upper {s : ℂ} (hs : 0 < s.re) {N : ℕ}
    (hN : 3 * (‖s‖ * ‖s + 1‖) ≤ (N : ℝ) + 1) :
    ‖dqptAltTail s N‖ ≤ 3 / 4 * ((N : ℝ) + 1) ^ (-s.re) := by
  have hM0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hd := (dqptAltTail_sub_half_norm_le hs N).trans (dqpt_threshold_bound hN)
  have hgn : ‖(1 / 2 : ℂ) * dqptRp s ((N : ℝ) + 1)‖ = 1 / 2 * ((N : ℝ) + 1) ^ (-s.re) := by
    rw [norm_mul, dqptRp_norm hM0]
    norm_num
  have htri : ‖dqptAltTail s N‖
      ≤ ‖dqptAltTail s N - (1 / 2 : ℂ) * dqptRp s ((N : ℝ) + 1)‖
        + ‖(1 / 2 : ℂ) * dqptRp s ((N : ℝ) + 1)‖ := by
    have := norm_add_le (dqptAltTail s N - (1 / 2 : ℂ) * dqptRp s ((N : ℝ) + 1))
      ((1 / 2 : ℂ) * dqptRp s ((N : ℝ) + 1))
    simpa using this
  rw [hgn] at htri
  linarith

end

end RHTower.DQPT
