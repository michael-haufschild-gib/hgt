import GaloisForLFunctions.HTGeometry.RpowHarmonicTailAsymptotic

/-!
# The weighted tail of a convergent sequence

If `g n → c` then the tail `∑_{m > n} g_m m^{p-2}` inherits the sharp asymptotic of the pure power
tail: renormalised by `n^{1-p}` it tends to `c/(1-p)` for every `p < 1`.  Splitting off the
constant part reduces the statement to the pure power tail plus an error bounded by
`sup_{m > n}|g_m − c|` times the same tail, which is uniformly comparable to `n^{p-1}`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **The weighted tail asymptotic.**  A convergent weight passes through the sharp power tail. -/
theorem tendsto_weightedTail_rpow {p c : ℝ} (hp : p < 1) {g : ℕ → ℝ}
    (hg : Tendsto g atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - p)
        * ∑' k : ℕ, g (n + 1 + k) * ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2))
      atTop (𝓝 (c / (1 - p))) := by
  have hq : p - 1 < 0 := by linarith
  have hqe : -(p - 1) = 1 - p := by ring
  have hqe2 : p - 1 - 1 = p - 2 := by ring
  -- the pure power tail
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - p)
      * ∑' k : ℕ, ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2)) atTop (𝓝 (1 / (1 - p))) := by
    have h := tendsto_tsum_shift_rpow hq
    rw [hqe] at h
    simpa only [hqe2] using h
  have hsummS : ∀ n : ℕ, Summable fun k : ℕ => ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2) := by
    intro n
    have h := summable_shift_rpow hq n
    simpa only [hqe2] using h
  -- a convergent sequence is bounded
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ n : ℕ, ‖g n‖ ≤ B := by
    obtain ⟨B, hB⟩ := (hg.norm).bddAbove_range
    exact ⟨B, fun n => hB ⟨n, rfl⟩⟩
  have hsummT : ∀ n : ℕ,
      Summable fun k : ℕ => g (n + 1 + k) * ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2) := by
    intro n
    refine Summable.of_norm_bounded ((hsummS n).mul_left B) fun k => ?_
    have hw : (0 : ℝ) ≤ ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2) := by
      have : (0 : ℝ) ≤ (n : ℝ) + 1 + (k : ℝ) := by positivity
      exact Real.rpow_nonneg this _
    rw [norm_mul, Real.norm_of_nonneg hw]
    exact mul_le_mul_of_nonneg_right (hB (n + 1 + k)) hw
  -- the constant part
  have hconst : Tendsto (fun n : ℕ => c * ((n : ℝ) ^ (1 - p)
      * ∑' k : ℕ, ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2))) atTop (𝓝 (c * (1 / (1 - p)))) :=
    hbase.const_mul c
  -- the error part
  have herr : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - p)
      * ∑' k : ℕ, (g (n + 1 + k) - c) * ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2)) atTop (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    have hposp : (0 : ℝ) < 1 - p := by linarith
    have hbound : (0 : ℝ) < 2 / (1 - p) := by positivity
    set δ : ℝ := ε / (2 * (2 / (1 - p))) with hδ
    have hδpos : 0 < δ := by
      rw [hδ]
      positivity
    obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
      (NormedAddGroup.tendsto_nhds_zero.1 (by simpa using hg.sub_const c) δ hδpos)
    have htail : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 - p)
        * ∑' k : ℕ, ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2) < 2 / (1 - p) := by
      have := hbase.eventually (eventually_lt_nhds (by
        rw [div_lt_div_iff₀ hposp hposp]
        nlinarith : (1 : ℝ) / (1 - p) < 2 / (1 - p)))
      exact this
    filter_upwards [eventually_ge_atTop n₀, htail] with n hn hlt
    have hSnn : (0 : ℝ) ≤ ∑' k : ℕ, ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2) := by
      refine tsum_nonneg fun k => ?_
      have : (0 : ℝ) ≤ (n : ℝ) + 1 + (k : ℝ) := by positivity
      exact Real.rpow_nonneg this _
    have hnp : (0 : ℝ) ≤ (n : ℝ) ^ (1 - p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hsummE : Summable fun k : ℕ =>
        ‖(g (n + 1 + k) - c) * ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2)‖ := by
      refine Summable.of_nonneg_of_le (fun k => norm_nonneg _)
        (fun k => ?_) ((hsummS n).mul_left δ)
      have hw : (0 : ℝ) ≤ ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2) := by
        have : (0 : ℝ) ≤ (n : ℝ) + 1 + (k : ℝ) := by positivity
        exact Real.rpow_nonneg this _
      rw [norm_mul, Real.norm_of_nonneg hw]
      exact mul_le_mul_of_nonneg_right (le_of_lt (hn₀ (n + 1 + k) (by omega))) hw
    have hnorm : ‖∑' k : ℕ, (g (n + 1 + k) - c) * ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2)‖
        ≤ δ * ∑' k : ℕ, ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2) := by
      refine le_trans (norm_tsum_le_tsum_norm hsummE) ?_
      refine le_trans (Summable.tsum_le_tsum (fun k => ?_) hsummE ((hsummS n).mul_left δ)) ?_
      · have hw : (0 : ℝ) ≤ ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2) := by
          have : (0 : ℝ) ≤ (n : ℝ) + 1 + (k : ℝ) := by positivity
          exact Real.rpow_nonneg this _
        rw [norm_mul, Real.norm_of_nonneg hw]
        exact mul_le_mul_of_nonneg_right (le_of_lt (hn₀ (n + 1 + k) (by omega))) hw
      · rw [tsum_mul_left]
    rw [norm_mul, Real.norm_of_nonneg hnp]
    have hstep : (n : ℝ) ^ (1 - p)
        * ‖∑' k : ℕ, (g (n + 1 + k) - c) * ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2)‖
        ≤ δ * ((n : ℝ) ^ (1 - p) * ∑' k : ℕ, ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2)) := by
      have := mul_le_mul_of_nonneg_left hnorm hnp
      linarith [this]
    have hlt2 : δ * ((n : ℝ) ^ (1 - p) * ∑' k : ℕ, ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2))
        < δ * (2 / (1 - p)) := by
      exact mul_lt_mul_of_pos_left hlt hδpos
    have hfin : δ * (2 / (1 - p)) < ε := by
      rw [hδ]
      rw [div_mul_eq_mul_div, mul_comm]
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [hbound, hε]
    linarith [hstep, hlt2, hfin]
  -- assemble
  have hsplit : ∀ n : ℕ, (n : ℝ) ^ (1 - p)
      * ∑' k : ℕ, g (n + 1 + k) * ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2)
      = (n : ℝ) ^ (1 - p)
          * ∑' k : ℕ, (g (n + 1 + k) - c) * ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2)
        + c * ((n : ℝ) ^ (1 - p) * ∑' k : ℕ, ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2)) := by
    intro n
    have hsummE : Summable fun k : ℕ =>
        (g (n + 1 + k) - c) * ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2) := by
      have h1 := hsummT n
      have h2 := (hsummS n).mul_left c
      have := h1.sub h2
      refine this.congr fun k => ?_
      ring
    have hdecomp : ∑' k : ℕ, g (n + 1 + k) * ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2)
        = (∑' k : ℕ, (g (n + 1 + k) - c) * ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2))
          + c * ∑' k : ℕ, ((n : ℝ) + 1 + (k : ℝ)) ^ (p - 2) := by
      rw [← tsum_mul_left, ← hsummE.tsum_add ((hsummS n).mul_left c)]
      refine tsum_congr fun k => ?_
      ring
    rw [hdecomp]
    ring
  have hfinal := herr.add hconst
  rw [zero_add] at hfinal
  have hval : c * (1 / (1 - p)) = c / (1 - p) := by ring
  rw [hval] at hfinal
  refine hfinal.congr fun n => ?_
  rw [hsplit n]

end GaloisForLFunctions.HTGeometry
