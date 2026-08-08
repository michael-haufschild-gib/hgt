import GaloisForLFunctions.RHTower.Sieve.MertensWindowSharp

/-!
# Prime windows cut at fixed exponents of the scale

For a fixed exponent `c > 0` the cutoff `⌊N^c⌋` satisfies `log ⌊N^c⌋ = c log N + O(1)`, so its
iterated logarithm is `logLog N + log c + o(1)`.  Feeding that into the sharp prime-window law gives
the exponent-window limit

`Σ_{N^a < p ≤ N^b} 1/p → log b - log a`   (`0 < a ≤ b`),

which is the step-function case of the prime-profile transfer: the reciprocal prime measure, read
in the exponent coordinate `t = log p / log N`, converges to `dt/t`.

The `O(1)` in `log ⌊N^c⌋ = c log N + O(1)` is `log 2`, coming only from `x - 1 < ⌊x⌋ ≤ x`.
-/

namespace RHTower.Sieve

open Filter Finset
open scoped Topology

noncomputable section

/-- The cutoff at a fixed exponent of the scale. -/
def exponentCutoff (c : ℝ) (N : ℕ) : ℕ := ⌊(N : ℝ) ^ c⌋₊

theorem tendsto_rpow_natCast_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ c) atTop atTop :=
  (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop

theorem eventually_le_rpow_natCast {c : ℝ} (hc : 0 < c) (r : ℝ) :
    ∀ᶠ N : ℕ in atTop, r ≤ (N : ℝ) ^ c :=
  (tendsto_rpow_natCast_atTop hc).eventually_ge_atTop r

/-- Two-sided control of the cutoff logarithm. -/
theorem abs_log_exponentCutoff_sub_le {c : ℝ} (hc : 0 < c) {N : ℕ}
    (hN : (2 : ℝ) ≤ (N : ℝ) ^ c) :
    |Real.log (exponentCutoff c N) - c * Real.log N| ≤ Real.log 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · exfalso
      rw [Nat.cast_zero, Real.zero_rpow (ne_of_gt hc)] at hN
      linarith
    · exact_mod_cast hpos
  have hlogrpow : Real.log ((N : ℝ) ^ c) = c * Real.log N := Real.log_rpow hNpos c
  have hfloor_le : ((exponentCutoff c N : ℕ) : ℝ) ≤ (N : ℝ) ^ c :=
    Nat.floor_le (by positivity)
  have hlt : (N : ℝ) ^ c - 1 < ((exponentCutoff c N : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one ((N : ℝ) ^ c)
    rw [exponentCutoff]
    linarith
  have hhalf : (N : ℝ) ^ c / 2 ≤ ((exponentCutoff c N : ℕ) : ℝ) := by
    have : (N : ℝ) ^ c / 2 ≤ (N : ℝ) ^ c - 1 := by linarith
    linarith
  have hfloorpos : (0 : ℝ) < ((exponentCutoff c N : ℕ) : ℝ) := by
    have : (0 : ℝ) < (N : ℝ) ^ c / 2 := by linarith
    linarith
  have hupper : Real.log (exponentCutoff c N) ≤ c * Real.log N := by
    rw [← hlogrpow]
    exact Real.log_le_log hfloorpos hfloor_le
  have hlower : c * Real.log N - Real.log 2 ≤ Real.log (exponentCutoff c N) := by
    have hstep : Real.log ((N : ℝ) ^ c / 2) ≤ Real.log (exponentCutoff c N) :=
      Real.log_le_log (by linarith) hhalf
    rw [Real.log_div (by positivity) (by norm_num), hlogrpow] at hstep
    linarith
  rw [abs_le]
  exact ⟨by linarith, by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]⟩

theorem tendsto_log_natCast_atTop' : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- **The exponent coordinate of the cutoff.**  `log ⌊N^c⌋ / log N → c`. -/
theorem tendsto_log_exponentCutoff_div {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => Real.log (exponentCutoff c N) / Real.log N) atTop (𝓝 c) := by
  have hzero : Tendsto (fun N : ℕ => Real.log 2 / Real.log N) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_log_natCast_atTop'
  have hsq : Tendsto (fun N : ℕ => Real.log (exponentCutoff c N) / Real.log N - c)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hzero
    filter_upwards [eventually_le_rpow_natCast hc 2, eventually_gt_atTop 1] with N hN hN1
    have hNpos : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hlogpos : (0 : ℝ) < Real.log N := Real.log_pos hNpos
    have hkey := abs_log_exponentCutoff_sub_le hc hN
    have hrw : Real.log (exponentCutoff c N) / Real.log N - c =
        (Real.log (exponentCutoff c N) - c * Real.log N) / Real.log N := by
      field_simp
    rw [Real.norm_eq_abs, hrw, abs_div, abs_of_pos hlogpos]
    gcongr
  have := hsq.add (tendsto_const_nhds (x := c) (f := (atTop : Filter ℕ)))
  simpa using this

/-- **The iterated logarithm of an exponent cutoff.**  `logLog ⌊N^c⌋ - logLog N → log c`. -/
theorem tendsto_logLog_exponentCutoff_sub {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => logLog (exponentCutoff c N) - logLog N) atTop (𝓝 (Real.log c)) := by
  have hdiv := tendsto_log_exponentCutoff_div hc
  have hcomp : Tendsto
      (fun N : ℕ => Real.log (Real.log (exponentCutoff c N) / Real.log N)) atTop
      (𝓝 (Real.log c)) :=
    (Real.continuousAt_log (ne_of_gt hc)).tendsto.comp hdiv
  refine hcomp.congr' ?_
  filter_upwards [eventually_le_rpow_natCast hc 4, eventually_gt_atTop 1] with N hN hN1
  have hNpos : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hlogpos : (0 : ℝ) < Real.log N := Real.log_pos hNpos
  have hfloorge : (2 : ℝ) ≤ ((exponentCutoff c N : ℕ) : ℝ) := by
    have hlt : (N : ℝ) ^ c - 1 < ((exponentCutoff c N : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one ((N : ℝ) ^ c)
      rw [exponentCutoff]
      linarith
    linarith
  have hfloorlog : (0 : ℝ) < Real.log (exponentCutoff c N) :=
    Real.log_pos (by linarith)
  rw [logLog, logLog, ← Real.log_div (ne_of_gt hfloorlog) (ne_of_gt hlogpos)]

/-- **The exponent-window prime reciprocal limit.**  Read in the exponent coordinate, the prime
reciprocal measure converges to `dt/t`. -/
theorem tendsto_sum_inv_exponentWindow {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun N : ℕ =>
        ∑ p ∈ bigPrimeSet (exponentCutoff a N) (exponentCutoff b N), 1 / (p : ℝ))
      atTop (𝓝 (Real.log b - Real.log a)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hCa := tendsto_logLog_exponentCutoff_sub ha
  have hCb := tendsto_logLog_exponentCutoff_sub hb
  have hdiff : Tendsto
      (fun N : ℕ => logLog (exponentCutoff b N) - logLog (exponentCutoff a N)) atTop
      (𝓝 (Real.log b - Real.log a)) := by
    have := hCb.sub hCa
    refine this.congr ?_
    intro N
    ring
  -- the two sharp Mertens errors vanish
  have herr : ∀ c : ℝ, 0 < c →
      Tendsto (fun N : ℕ =>
        mertensS (exponentCutoff c N) - logLog (exponentCutoff c N) - meisselMertensConst)
        atTop (𝓝 0) := by
    intro c hc
    have hlogto : Tendsto (fun N : ℕ => Real.log (exponentCutoff c N)) atTop atTop := by
      have hsub : Tendsto (fun N : ℕ => (N : ℝ) ^ c + (-1)) atTop atTop :=
        Filter.tendsto_atTop_add_const_right atTop (-1) (tendsto_rpow_natCast_atTop hc)
      have hcast : Tendsto (fun N : ℕ => ((exponentCutoff c N : ℕ) : ℝ)) atTop atTop := by
        refine tendsto_atTop_mono' atTop ?_ hsub
        filter_upwards [] with N
        have hfl := Nat.lt_floor_add_one ((N : ℝ) ^ c)
        rw [exponentCutoff]
        linarith
      exact Real.tendsto_log_atTop.comp hcast
    have hzero : Tendsto
        (fun N : ℕ => (2 * mertensFirstConst + 1 / 2) / Real.log (exponentCutoff c N))
        atTop (𝓝 0) := Tendsto.div_atTop tendsto_const_nhds hlogto
    refine squeeze_zero_norm' ?_ hzero
    filter_upwards [eventually_le_rpow_natCast hc 4, eventually_gt_atTop 1] with N hN hN1
    have hfloorge : (2 : ℝ) ≤ ((exponentCutoff c N : ℕ) : ℝ) := by
      have hlt : (N : ℝ) ^ c - 1 < ((exponentCutoff c N : ℕ) : ℝ) := by
        have := Nat.lt_floor_add_one ((N : ℝ) ^ c)
        rw [exponentCutoff]
        linarith
      linarith
    have hfloorNat : 2 ≤ exponentCutoff c N := by exact_mod_cast hfloorge
    simpa [Real.norm_eq_abs] using abs_mertensS_sub_logLog_sub_const_le hfloorNat
  have hmain : Tendsto (fun N : ℕ =>
      (mertensS (exponentCutoff b N) - logLog (exponentCutoff b N) - meisselMertensConst
        - (mertensS (exponentCutoff a N) - logLog (exponentCutoff a N) - meisselMertensConst))
        + (logLog (exponentCutoff b N) - logLog (exponentCutoff a N)))
      atTop (𝓝 (Real.log b - Real.log a)) := by
    have h := ((herr b hb).sub (herr a ha)).add hdiff
    simpa using h
  refine hmain.congr' ?_
  filter_upwards [eventually_le_rpow_natCast ha 4, eventually_le_rpow_natCast hb 4,
    eventually_gt_atTop 1] with N hNa hNb hN1
  have hmono : exponentCutoff a N ≤ exponentCutoff b N := by
    refine Nat.floor_le_floor ?_
    have hNge : (1 : ℝ) ≤ (N : ℝ) := by
      have : (1 : ℕ) ≤ N := le_of_lt hN1
      exact_mod_cast this
    exact Real.rpow_le_rpow_of_exponent_le hNge hab
  rw [sum_inv_bigPrimeSet _ _ hmono]
  ring

end

end RHTower.Sieve
