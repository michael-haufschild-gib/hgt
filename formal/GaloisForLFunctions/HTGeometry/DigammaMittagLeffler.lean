import GaloisForLFunctions.HTGeometry.DigammaAsymptotic

/-!
# The Mittag-Leffler series of the digamma function

For `Re s > 0`,

`ψ(s) = −γ + Σ_{k ≥ 0} (1/(k+1) − 1/(s+k))`,

with the series absolutely convergent.  The proof combines Gauss's limit formula
`ψ(s) = lim_n (log n − Σ_{j ≤ n} 1/(s+j))` with `H_n − log n → γ`: the partial sums of the series are
`H_n − Σ_{j<n} 1/(s+j) = (H_n − log n) + (log n − Σ_{j≤n} 1/(s+j)) + 1/(s+n)`.
-/

open Complex Filter Topology

namespace RHTower

/-- The terms `1/(k+1) − 1/(s+k)` are absolutely summable for `Re s > 0`: each is
`(s−1)/((k+1)(s+k))`, and `|s+k| ≥ min(Re s, 1)·(k+1)`. -/
theorem summable_digammaSeriesTerm {s : ℂ} (hs : 0 < s.re) :
    Summable (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / (s + k)) := by
  set c : ℝ := min s.re 1 with hc
  have hc0 : 0 < c := lt_min hs one_pos
  have hc1 : c ≤ 1 := min_le_right _ _
  have hcs : c ≤ s.re := min_le_left _ _
  have hbound : ∀ k : ℕ, ‖1 / ((k : ℂ) + 1) - 1 / (s + k)‖ ≤ (‖s - 1‖ / c) * (1 / ((k : ℝ) + 1) ^ (2 : ℕ)) := by
    intro k
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
    have hsk_re : c * ((k : ℝ) + 1) ≤ (s + k).re := by
      rw [Complex.add_re, Complex.natCast_re]
      nlinarith [hcs, hc1, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have hsk_norm : c * ((k : ℝ) + 1) ≤ ‖s + k‖ := hsk_re.trans (Complex.re_le_norm _)
    have hsk : s + k ≠ 0 := by
      intro h; rw [h, norm_zero] at hsk_norm; nlinarith [hc0, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have hident : 1 / ((k : ℂ) + 1) - 1 / (s + k) = (s - 1) / (((k : ℂ) + 1) * (s + k)) := by
      field_simp; ring
    rw [hident, norm_div, norm_mul]
    have hk1n : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
      rw [show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]; push_cast; ring
    rw [hk1n]
    have hpos : 0 < ((k : ℝ) + 1) := by positivity
    rw [div_le_iff₀ (by positivity)]
    calc ‖s - 1‖ = (‖s - 1‖ / c) * (1 / ((k : ℝ) + 1) ^ (2 : ℕ)) * (((k : ℝ) + 1) * (c * ((k : ℝ) + 1))) := by
          field_simp
      _ ≤ (‖s - 1‖ / c) * (1 / ((k : ℝ) + 1) ^ (2 : ℕ)) * (((k : ℝ) + 1) * ‖s + k‖) := by
          gcongr
  refine Summable.of_norm_bounded (g := fun k : ℕ => (‖s - 1‖ / c) * (1 / ((k : ℝ) + 1) ^ (2 : ℕ))) ?_ hbound
  have h2 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ (2 : ℕ)) := by
    have := (Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two
    exact_mod_cast (summable_nat_add_iff 1).mpr this
  exact h2.mul_left _

/-- `1/(s+n) → 0` for `Re s > 0`, since `‖s+n‖ ≥ Re s + n ≥ n`. -/
theorem tendsto_one_div_add_natCast {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => 1 / (s + (n : ℂ))) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat 1)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hre : (n : ℝ) ≤ (s + n).re := by
    rw [Complex.add_re, Complex.natCast_re]; linarith
  have hnorm : (n : ℝ) ≤ ‖s + n‖ := hre.trans (Complex.re_le_norm _)
  rw [norm_div, norm_one]
  exact one_div_le_one_div_of_le (by linarith) hnorm

/-- `H_n − log n → γ`, complex form. -/
theorem tendsto_harmonic_sub_log_complex :
    Tendsto (fun n : ℕ => ((harmonic n : ℝ) : ℂ) - Complex.log (n : ℂ)) atTop
      (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
  have h := Real.tendsto_harmonic_sub_log.ofReal
  refine h.congr fun n => ?_
  rw [Complex.ofReal_sub, Complex.ofReal_log (Nat.cast_nonneg n), Complex.ofReal_natCast]

/-- **The Mittag-Leffler series of the digamma function.**  For `Re s > 0`,
`Σ_{k≥0} (1/(k+1) − 1/(s+k)) = ψ(s) + γ`. -/
theorem hasSum_digammaSeries {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / (s + k))
      (Complex.digamma s + Real.eulerMascheroniConstant) := by
  rw [(summable_digammaSeriesTerm hs).hasSum_iff_tendsto_nat]
  have hG := gauss_digamma hs
  have hH := tendsto_harmonic_sub_log_complex
  have hT := tendsto_one_div_add_natCast hs
  have h := (hH.add hG).add hT
  rw [add_zero, add_comm] at h
  refine h.congr fun n => ?_
  rw [Finset.sum_sub_distrib, harmonic_cast_eq n, Finset.sum_range_succ]
  ring

theorem digamma_eq_tsum {s : ℂ} (hs : 0 < s.re) :
    Complex.digamma s =
      -(Real.eulerMascheroniConstant : ℂ) + ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / (s + k)) := by
  rw [(hasSum_digammaSeries hs).tsum_eq]; ring

end RHTower
