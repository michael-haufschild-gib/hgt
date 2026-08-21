import GaloisForLFunctions.RHTower.DQPTPartialSumRate

/-!
# DQPT: the first normal of the alternating partial sum and the reflected slope law

This module records the positive survivor extracted in
`docs/drafts/pipeline/5-failed/nature-dqpt-alternating-tail-rh-route.md` from the DQPT paper
(arXiv:2511.11199): at a zero of the Dirichlet eta function the partial sum has the exact
**first normal**

`(−1)^{N+1}(N+1)^{s} S_N(s) → 1/2`,

so the raw decay rate of `S_N` at a zero `ρ = β + iγ` is `β`, and at the reflected zero
`ρ† = 1 − β + iγ` it is `1 − β`.  Consequently

`|S_N(ρ)| / |S_N(ρ†)| ≍ (N+1)^{1−2β}`,

and the two reflected rates agree exactly when `Re ρ = 1/2` — the card's equations (1)–(3).

Main results:
* `dqpt_altTail_normal_tendsto` — the first normal `(N+1)^s A_N(s) → 1/2`;
* `dqpt_altPartialSum_normal_tendsto` — the same for `S_N` up to the parity sign;
* `dqpt_reflected_ratio_bounds` — the two-sided form of the card's (1);
* `dqpt_reflected_rates_eq_iff` — the card's (2): equal reflected rates ⟺ `Re ρ = 1/2`.
-/

namespace RHTower.DQPT

open Complex Filter Topology Set

noncomputable section

/-! ## The first normal at an eta zero -/

/-- `(N+1)^{s}·A_N(s) → 1/2`: the exact first normal of the paired tail. -/
theorem dqpt_altTail_normal_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => dqptRp (-s) ((N : ℝ) + 1) * dqptAltTail s N) atTop (𝓝 (1 / 2)) := by
  have hmaj : Tendsto
      (fun N : ℕ => 3 / 4 * (‖s‖ * ‖s + 1‖) * ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have hbase : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hbase
    simpa using hinv.const_mul (3 / 4 * (‖s‖ * ‖s + 1‖))
  have hbound : ∀ᶠ N : ℕ in atTop,
      ‖dqptRp (-s) ((N : ℝ) + 1) * dqptAltTail s N - 1 / 2‖
        ≤ 3 / 4 * (‖s‖ * ‖s + 1‖) * ((N : ℝ) + 1)⁻¹ := by
    filter_upwards with N
    have hM0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hMne : (((N : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hM0)
    have hmulinv : dqptRp (-s) ((N : ℝ) + 1) * dqptRp s ((N : ℝ) + 1) = 1 := by
      rw [dqptRp, dqptRp, ← Complex.cpow_add _ _ hMne]
      simp
    have hfactor : dqptRp (-s) ((N : ℝ) + 1) * dqptAltTail s N - 1 / 2
        = dqptRp (-s) ((N : ℝ) + 1)
            * (dqptAltTail s N - (1 / 2 : ℂ) * dqptRp s ((N : ℝ) + 1)) := by
      have h := hmulinv
      linear_combination ((1 : ℂ) / 2) * h
    rw [hfactor, norm_mul]
    have hnorm : ‖dqptRp (-s) ((N : ℝ) + 1)‖ = ((N : ℝ) + 1) ^ (s.re) := by
      rw [dqptRp_norm hM0]
      congr 1
      simp
    rw [hnorm]
    have hstep := dqptAltTail_sub_half_norm_le hs N
    have hpow : ((N : ℝ) + 1) ^ s.re * ((N : ℝ) + 1) ^ (-s.re - 1) = ((N : ℝ) + 1)⁻¹ := by
      rw [← Real.rpow_add hM0]
      have hz : s.re + (-s.re - 1) = -1 := by ring
      rw [hz, Real.rpow_neg_one]
    calc ((N : ℝ) + 1) ^ s.re * ‖dqptAltTail s N - (1 / 2 : ℂ) * dqptRp s ((N : ℝ) + 1)‖
        ≤ ((N : ℝ) + 1) ^ s.re * (3 / 4 * (‖s‖ * ‖s + 1‖) * ((N : ℝ) + 1) ^ (-s.re - 1)) :=
          mul_le_mul_of_nonneg_left hstep (le_of_lt (Real.rpow_pos_of_pos hM0 _))
      _ = 3 / 4 * (‖s‖ * ‖s + 1‖)
            * (((N : ℝ) + 1) ^ s.re * ((N : ℝ) + 1) ^ (-s.re - 1)) := by ring
      _ = 3 / 4 * (‖s‖ * ‖s + 1‖) * ((N : ℝ) + 1)⁻¹ := by rw [hpow]
  have hzero : Tendsto
      (fun N : ℕ => dqptRp (-s) ((N : ℝ) + 1) * dqptAltTail s N - 1 / 2) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero_norm' (by filter_upwards [hbound] with N h; simpa using h) hmaj
  have := hzero.add (tendsto_const_nhds (x := (1 / 2 : ℂ)) (f := atTop (α := ℕ)))
  simpa using this

/-- The same normal for the partial sum at an eta zero, up to the parity sign. -/
theorem dqpt_altPartialSum_normal_tendsto {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hz : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s = 0) :
    Tendsto (fun N : ℕ =>
        (-1 : ℂ) ^ (N + 1) * (dqptRp (-s) ((N : ℝ) + 1) * dqptAltPartialSum s N))
      atTop (𝓝 (1 / 2)) := by
  have heq : ∀ N : ℕ,
      (-1 : ℂ) ^ (N + 1) * (dqptRp (-s) ((N : ℝ) + 1) * dqptAltPartialSum s N)
        = dqptRp (-s) ((N : ℝ) + 1) * dqptAltTail s N := by
    intro N
    have h := dqptEta_eq_altPartialSum_add_tail hs hs1 N
    rw [hz] at h
    have hS : dqptAltPartialSum s N = -((-1 : ℂ) ^ N * dqptAltTail s N) := by
      linear_combination -h
    have hsign : ((-1 : ℂ) ^ (N + 1)) * (-((-1 : ℂ) ^ N)) = 1 := by
      rw [pow_succ]
      have : ((-1 : ℂ) ^ N) * ((-1 : ℂ) ^ N) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]
        norm_num
      linear_combination this
    rw [hS]
    linear_combination (dqptRp (-s) ((N : ℝ) + 1) * dqptAltTail s N) * hsign
  exact Tendsto.congr (fun N => (heq N).symm) (dqpt_altTail_normal_tendsto hs)

/-! ## The reflected slope law -/

/-- **Card equation (1), two-sided form.**  At two eta zeros `s`, `s'` the ratio of the partial
sums is pinned to `(N+1)^{Re s' − Re s}` up to the absolute constant `3`. -/
theorem dqpt_reflected_ratio_bounds {s s' : ℂ} (hs : 0 < s.re) (hs' : 0 < s'.re)
    (hs1 : s ≠ 1) (hs1' : s' ≠ 1)
    (hz : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s = 0)
    (hz' : (1 - (2 : ℂ) ^ (1 - s')) * riemannZeta s' = 0)
    {N : ℕ} (hN : 3 * (‖s‖ * ‖s + 1‖) ≤ (N : ℝ) + 1)
    (hN' : 3 * (‖s'‖ * ‖s' + 1‖) ≤ (N : ℝ) + 1) :
    (1 / 3) * ((N : ℝ) + 1) ^ (s'.re - s.re)
        ≤ ‖dqptAltPartialSum s N‖ / ‖dqptAltPartialSum s' N‖
      ∧ ‖dqptAltPartialSum s N‖ / ‖dqptAltPartialSum s' N‖
        ≤ 3 * ((N : ℝ) + 1) ^ (s'.re - s.re) := by
  have hM0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hnorm : ∀ {w : ℂ}, 0 < w.re → w ≠ 1 →
      (1 - (2 : ℂ) ^ (1 - w)) * riemannZeta w = 0 →
      ‖dqptAltPartialSum w N‖ = ‖dqptAltTail w N‖ := by
    intro w hw hw1 hwz
    have h := dqptEta_eq_altPartialSum_add_tail hw hw1 N
    rw [hwz] at h
    have hS : dqptAltPartialSum w N = -((-1 : ℂ) ^ N * dqptAltTail w N) := by
      linear_combination -h
    rw [hS, norm_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [hnorm hs hs1 hz, hnorm hs' hs1' hz']
  have hlow := dqptAltTail_norm_lower hs hN
  have hupp := dqptAltTail_norm_upper hs hN
  have hlow' := dqptAltTail_norm_lower hs' hN'
  have hupp' := dqptAltTail_norm_upper hs' hN'
  have hpos : (0 : ℝ) < ((N : ℝ) + 1) ^ (-s.re) := Real.rpow_pos_of_pos hM0 _
  have hpos' : (0 : ℝ) < ((N : ℝ) + 1) ^ (-s'.re) := Real.rpow_pos_of_pos hM0 _
  have hApos : 0 < ‖dqptAltTail s N‖ := lt_of_lt_of_le (by positivity) hlow
  have hApos' : 0 < ‖dqptAltTail s' N‖ := lt_of_lt_of_le (by positivity) hlow'
  have hratio : ((N : ℝ) + 1) ^ (-s.re) / ((N : ℝ) + 1) ^ (-s'.re)
      = ((N : ℝ) + 1) ^ (s'.re - s.re) := by
    rw [← Real.rpow_sub hM0]
    congr 1
    ring
  constructor
  · rw [le_div_iff₀ hApos']
    have hstep : 1 / 3 * ((N : ℝ) + 1) ^ (s'.re - s.re) * ‖dqptAltTail s' N‖
        ≤ 1 / 3 * ((N : ℝ) + 1) ^ (s'.re - s.re) * (3 / 4 * ((N : ℝ) + 1) ^ (-s'.re)) := by
      refine mul_le_mul_of_nonneg_left hupp' ?_
      positivity
    refine hstep.trans ?_
    have hval : 1 / 3 * ((N : ℝ) + 1) ^ (s'.re - s.re) * (3 / 4 * ((N : ℝ) + 1) ^ (-s'.re))
        = 1 / 4 * ((N : ℝ) + 1) ^ (-s.re) := by
      rw [← hratio]
      field_simp
    rw [hval]
    exact hlow
  · rw [div_le_iff₀ hApos']
    have hstep : ‖dqptAltTail s N‖ ≤ 3 / 4 * ((N : ℝ) + 1) ^ (-s.re) := hupp
    refine hstep.trans ?_
    have hval : 3 / 4 * ((N : ℝ) + 1) ^ (-s.re)
        = 3 * ((N : ℝ) + 1) ^ (s'.re - s.re) * (1 / 4 * ((N : ℝ) + 1) ^ (-s'.re)) := by
      rw [← hratio]
      field_simp
    rw [hval]
    refine mul_le_mul_of_nonneg_left hlow' ?_
    positivity

/-- **Card equation (2).**  The two reflected raw tail rates `β ln2` and `(1−β) ln2` agree exactly
on the critical line. -/
theorem dqpt_reflected_rates_eq_iff {β : ℝ} :
    β * Real.log 2 = (1 - β) * Real.log 2 ↔ β = 1 / 2 := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  constructor
  · intro h
    have := mul_right_cancel₀ hlog h
    linarith
  · intro h
    rw [h]
    ring_nf

end

end RHTower.DQPT
