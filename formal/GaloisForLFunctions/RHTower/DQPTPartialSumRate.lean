import GaloisForLFunctions.RHTower.DQPTTailNormal

/-!
# DQPT: the logarithmic rate of the alternating partial sum

**Supplementary Note 1 (1.21)** of arXiv:2511.11199 (published (17)):

`−(1/log₂ N)·ln|S_N(s)| → β ln 2` if `η(s) = 0`, and `→ 0` if `η(s) ≠ 0`,

where `η(s) = (1 − 2^{1−s})ζ(s)` and `s = β + it` with `β > 0`.

The paper states the dichotomy on `ζ(s)`.  That is correct exactly where the eta multiplier
`1 − 2^{1−s}` does not vanish, i.e. off the line `Re s = 1`; the intrinsic dichotomy is on `η`.
Both forms are recorded: `dqpt_rate_at_eta_zero` / `dqpt_rate_at_eta_ne_zero` and, in the open
critical strip, `dqpt_rate_at_zeta_zero` / `dqpt_rate_at_zeta_ne_zero`.

Main results:
* `dqpt_tendsto_neg_log_div_logb` — a two-sided power sandwich pins the logarithmic rate;
* `dqpt_altPartialSum_tendsto` — `S_N(s) → η(s)`;
* `dqpt_rate_at_eta_zero`, `dqpt_rate_at_eta_ne_zero` — **Supplementary Note 1 (1.21)**.
-/

namespace RHTower.DQPT

open Complex Filter Topology Set

noncomputable section

/-! ## A two-sided power sandwich pins the logarithmic rate -/

theorem dqpt_tendsto_log_natCast_atTop :
    Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem dqpt_tendsto_logb_natCast_atTop :
    Tendsto (fun N : ℕ => Real.logb 2 (N : ℝ)) atTop atTop := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have := dqpt_tendsto_log_natCast_atTop.atTop_div_const h2
  exact this.congr (fun N => by rw [Real.logb])

/-- **A two-sided power sandwich pins the logarithmic rate.**  If eventually
`c₁ N^{−a} ≤ u N ≤ c₂ N^{−a}` with `c₁, c₂ > 0`, then `−ln (u N)/log₂ N → a ln 2`. -/
theorem dqpt_tendsto_neg_log_div_logb {u : ℕ → ℝ} {a c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hlow : ∀ᶠ N : ℕ in atTop, c₁ * (N : ℝ) ^ (-a) ≤ u N)
    (hupp : ∀ᶠ N : ℕ in atTop, u N ≤ c₂ * (N : ℝ) ^ (-a)) :
    Tendsto (fun N : ℕ => -Real.log (u N) / Real.logb 2 (N : ℝ)) atTop
      (𝓝 (a * Real.log 2)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hbig : ∀ᶠ N : ℕ in atTop, (2 : ℕ) ≤ N := eventually_ge_atTop 2
  have hside : ∀ c : ℝ, Tendsto
      (fun N : ℕ => a * Real.log 2 - Real.log 2 * Real.log c / Real.log (N : ℝ))
      atTop (𝓝 (a * Real.log 2)) := by
    intro c
    have hzero : Tendsto (fun N : ℕ => Real.log 2 * Real.log c / Real.log (N : ℝ))
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop dqpt_tendsto_log_natCast_atTop
    simpa using (tendsto_const_nhds (x := a * Real.log 2)).sub hzero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hside c₂) (hside c₁) ?_ ?_
  · filter_upwards [hbig, hlow, hupp] with N hN hl hh
    have hN0 : (0 : ℝ) < (N : ℝ) := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hlogN : (0 : ℝ) < Real.log (N : ℝ) := by
      refine Real.log_pos ?_
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hlogb : (0 : ℝ) < Real.logb 2 (N : ℝ) := by
      rw [Real.logb]; positivity
    have hpow : (0 : ℝ) < (N : ℝ) ^ (-a) := Real.rpow_pos_of_pos hN0 _
    have hupos : 0 < u N := lt_of_lt_of_le (by positivity) hl
    have hlogu : Real.log (u N) ≤ Real.log c₂ + (-a) * Real.log (N : ℝ) := by
      calc Real.log (u N) ≤ Real.log (c₂ * (N : ℝ) ^ (-a)) := Real.log_le_log hupos hh
        _ = Real.log c₂ + (-a) * Real.log (N : ℝ) := by
            rw [Real.log_mul (ne_of_gt hc₂) (ne_of_gt hpow), Real.log_rpow hN0]
    rw [Real.logb, div_div_eq_mul_div, le_div_iff₀ hlogN]
    have hL : (a * Real.log 2 - Real.log 2 * Real.log c₂ / Real.log (N : ℝ))
        * Real.log (N : ℝ)
        = a * Real.log 2 * Real.log (N : ℝ) - Real.log 2 * Real.log c₂ := by
      field_simp
    rw [hL]
    nlinarith [hlogu, hlog2]
  · filter_upwards [hbig, hlow] with N hN hl
    have hN0 : (0 : ℝ) < (N : ℝ) := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hlogN : (0 : ℝ) < Real.log (N : ℝ) := by
      refine Real.log_pos ?_
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hpow : (0 : ℝ) < (N : ℝ) ^ (-a) := Real.rpow_pos_of_pos hN0 _
    have hupos : 0 < u N := lt_of_lt_of_le (by positivity) hl
    have hlogu : Real.log c₁ + (-a) * Real.log (N : ℝ) ≤ Real.log (u N) := by
      calc Real.log c₁ + (-a) * Real.log (N : ℝ)
          = Real.log (c₁ * (N : ℝ) ^ (-a)) := by
            rw [Real.log_mul (ne_of_gt hc₁) (ne_of_gt hpow), Real.log_rpow hN0]
        _ ≤ Real.log (u N) := Real.log_le_log (by positivity) hl
    rw [Real.logb, div_div_eq_mul_div, div_le_iff₀ hlogN]
    have hL : (a * Real.log 2 - Real.log 2 * Real.log c₁ / Real.log (N : ℝ))
        * Real.log (N : ℝ)
        = a * Real.log 2 * Real.log (N : ℝ) - Real.log 2 * Real.log c₁ := by
      field_simp
    rw [hL]
    nlinarith [hlogu, hlog2]

/-! ## The tail vanishes and the partial sum converges -/

theorem dqpt_eventually_threshold (s : ℂ) :
    ∀ᶠ N : ℕ in atTop, 3 * (‖s‖ * ‖s + 1‖) ≤ (N : ℝ) + 1 := by
  have h : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  exact h.eventually_ge_atTop _

theorem dqpt_tendsto_altTail_zero {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => dqptAltTail s N) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hmaj : Tendsto (fun N : ℕ => 3 / 4 * ((N : ℝ) + 1) ^ (-s.re)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have := (tendsto_rpow_neg_atTop hs).comp hbase
    simpa using this.const_mul (3 / 4 : ℝ)
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [dqpt_eventually_threshold s] with N hN
  simpa using dqptAltTail_norm_upper hs hN

/-- The alternating partial sum converges to `η(s) = (1 − 2^{1−s})ζ(s)`. -/
theorem dqpt_altPartialSum_tendsto {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Tendsto (fun N : ℕ => dqptAltPartialSum s N) atTop
      (𝓝 ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s)) := by
  have hsign : Tendsto (fun N : ℕ => (-1 : ℂ) ^ N * dqptAltTail s N) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hEq : ∀ N : ℕ, ‖(-1 : ℂ) ^ N * dqptAltTail s N‖ = ‖dqptAltTail s N‖ := by
      intro N; rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    refine Tendsto.congr (fun N => (hEq N).symm) ?_
    exact (tendsto_zero_iff_norm_tendsto_zero).mp (dqpt_tendsto_altTail_zero hs)
  have hid : ∀ N : ℕ, dqptAltPartialSum s N
      = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s - (-1 : ℂ) ^ N * dqptAltTail s N := by
    intro N
    have h := dqptEta_eq_altPartialSum_add_tail hs hs1 N
    linear_combination -h
  refine Tendsto.congr (fun N => (hid N).symm) ?_
  simpa using (tendsto_const_nhds
    (x := (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s)).sub hsign

/-! ## Supplementary Note 1 (1.21) -/

/-- **Case 1.**  At a zero of the Dirichlet eta function the rate is `β ln 2`. -/
theorem dqpt_rate_at_eta_zero {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hz : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s = 0) :
    Tendsto (fun N : ℕ => -Real.log ‖dqptAltPartialSum s N‖ / Real.logb 2 (N : ℝ)) atTop
      (𝓝 (s.re * Real.log 2)) := by
  have hnorm : ∀ N : ℕ, ‖dqptAltPartialSum s N‖ = ‖dqptAltTail s N‖ := by
    intro N
    have h := dqptEta_eq_altPartialSum_add_tail hs hs1 N
    rw [hz] at h
    have hs' : dqptAltPartialSum s N = -((-1 : ℂ) ^ N * dqptAltTail s N) := by
      linear_combination -h
    rw [hs', norm_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  refine Tendsto.congr (fun N => by rw [hnorm N]) ?_
  have hc₁ : (0 : ℝ) < (2 : ℝ) ^ (-s.re) / 4 := by positivity
  refine dqpt_tendsto_neg_log_div_logb (a := s.re) hc₁ (by norm_num : (0 : ℝ) < 3 / 4) ?_ ?_
  · filter_upwards [dqpt_eventually_threshold s, eventually_ge_atTop 1] with N hN hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hlow := dqptAltTail_norm_lower hs hN
    refine le_trans ?_ hlow
    have hle : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
      linarith
    have hmono : (2 * (N : ℝ)) ^ (-s.re) ≤ ((N : ℝ) + 1) ^ (-s.re) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hle (by linarith)
    have hsplit : (2 * (N : ℝ)) ^ (-s.re) = (2 : ℝ) ^ (-s.re) * (N : ℝ) ^ (-s.re) :=
      Real.mul_rpow (by norm_num) (le_of_lt hN0)
    calc (2 : ℝ) ^ (-s.re) / 4 * (N : ℝ) ^ (-s.re)
        = 1 / 4 * ((2 : ℝ) ^ (-s.re) * (N : ℝ) ^ (-s.re)) := by ring
      _ = 1 / 4 * (2 * (N : ℝ)) ^ (-s.re) := by rw [hsplit]
      _ ≤ 1 / 4 * ((N : ℝ) + 1) ^ (-s.re) :=
          mul_le_mul_of_nonneg_left hmono (by norm_num)
  · filter_upwards [dqpt_eventually_threshold s, eventually_ge_atTop 1] with N hN hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hupp := dqptAltTail_norm_upper hs hN
    refine hupp.trans ?_
    have hmono : ((N : ℝ) + 1) ^ (-s.re) ≤ (N : ℝ) ^ (-s.re) :=
      Real.rpow_le_rpow_of_nonpos hN0 (by linarith) (by linarith)
    exact mul_le_mul_of_nonneg_left hmono (by norm_num)

/-- **Case 2.**  Off the zero set of the Dirichlet eta function the rate is `0`. -/
theorem dqpt_rate_at_eta_ne_zero {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hz : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s ≠ 0) :
    Tendsto (fun N : ℕ => -Real.log ‖dqptAltPartialSum s N‖ / Real.logb 2 (N : ℝ)) atTop
      (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => -Real.log ‖dqptAltPartialSum s N‖) atTop
      (𝓝 (-Real.log ‖(1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s‖)) := by
    exact ((Real.continuousAt_log (by simpa using hz)).tendsto.comp
      ((dqpt_altPartialSum_tendsto hs hs1).norm)).neg
  simpa using hlim.div_atTop dqpt_tendsto_logb_natCast_atTop

/-! ## The `ζ`-form inside the open critical strip -/

theorem dqpt_eta_factor_ne_zero {s : ℂ} (hs : s.re ≠ 1) : (1 - (2 : ℂ) ^ (1 - s)) ≠ 0 := by
  intro h
  have h2 : (2 : ℂ) ^ (1 - s) = 1 := by linear_combination -h
  have hb : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  have hnorm : ‖(2 : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s.re) := by
    rw [← hb, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2), Complex.sub_re,
      Complex.one_re]
  rw [h2, norm_one] at hnorm
  have hpow : (2 : ℝ) ^ (1 - s.re) = 1 := hnorm.symm
  have hL : (1 - s.re) * Real.log 2 = 0 := by
    rw [← Real.log_rpow (by norm_num : (0 : ℝ) < 2), hpow, Real.log_one]
  have hzero : (1 : ℝ) - s.re = 0 := by
    rcases mul_eq_zero.mp hL with h' | h'
    · exact h'
    · exact absurd h' (ne_of_gt (Real.log_pos (by norm_num)))
  exact hs (by linarith)

/-- **Case 1 in the `ζ`-form** (valid off the line `Re s = 1`, in particular in the open
critical strip): at a zeta zero the rate is `β ln 2`. -/
theorem dqpt_rate_at_zeta_zero {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≠ 1)
    (hz : riemannZeta s = 0) :
    Tendsto (fun N : ℕ => -Real.log ‖dqptAltPartialSum s N‖ / Real.logb 2 (N : ℝ)) atTop
      (𝓝 (s.re * Real.log 2)) := by
  refine dqpt_rate_at_eta_zero hs (fun h => hs1 (by rw [h]; simp)) ?_
  rw [hz, mul_zero]

/-- **Case 2 in the `ζ`-form** (valid off the line `Re s = 1`): away from the zeta zeros the
rate is `0`. -/
theorem dqpt_rate_at_zeta_ne_zero {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    Tendsto (fun N : ℕ => -Real.log ‖dqptAltPartialSum s N‖ / Real.logb 2 (N : ℝ)) atTop
      (𝓝 0) :=
  dqpt_rate_at_eta_ne_zero hs (fun h => hs1 (by rw [h]; simp))
    (mul_ne_zero (dqpt_eta_factor_ne_zero hs1) hz)

end

end RHTower.DQPT
