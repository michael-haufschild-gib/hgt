import GaloisForLFunctions.RHTower.Sieve.GhsTopBlockBound

/-!
# The total error is `N·log log N`

The three error levels are each at most `N` times a constant or `N·log log N`, so their maximum is
too:

```text
ghsTotalError N (ghsHeight N) (ghsScaleCount N) σ
  ≤ N·(ghsErrorConst + ghsTopConst + 32 log 2 + 96 log log N) .
```

Multiplied by `K + 2 ≍ log log N` and divided by `N·log N`, this is `≍ (log log N)²/log N`, which
tends to zero — the second asymptotic input of the argument, and like the first it is a power of
`log` against a power of the identity.
-/

noncomputable section

namespace RHTower.Sieve

open Complex Filter Asymptotics Finset Topology

/-- `(log t)² = o(t)`. -/
theorem tendsto_sq_log_div_atTop : Tendsto (fun t : ℝ => (Real.log t) ^ 2 / t) atTop (𝓝 0) := by
  have hlo : (fun t : ℝ => Real.log t) =o[atTop] (fun t : ℝ => t ^ ((1 : ℝ) / 2)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have hpow := hlo.pow (n := 2) (by norm_num)
  have hdiv := hpow.tendsto_div_nhds_zero
  refine hdiv.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  have hrw : (t ^ ((1 : ℝ) / 2)) ^ 2 = t := by
    rw [← Real.rpow_natCast (t ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul ht.le]
    norm_num
  rw [hrw]

/-- `(log log N)² = o(log N)`. -/
theorem tendsto_sq_log_log_div_log :
    Tendsto (fun N : ℕ => (Real.log (Real.log N)) ^ 2 / Real.log N) atTop (𝓝 0) :=
  tendsto_sq_log_div_atTop.comp tendsto_log_natCast_atTop

/-- **The total error is `N·log log N`.** -/
theorem ghsTotalError_le {N : ℕ} {σ : ℝ} (hlogN : (3 : ℝ) ≤ Real.log N) (hN : 65536 ≤ N)
    (hroot : (ghsHeight N) ^ 2 ≤ ghsScale N 1) (hn2 : (ghsHeight N) ^ 2 ≤ N)
    (hx : ((N : ℝ) + 1 / 2) ^ σ ≤ 3 * (N : ℝ)) :
    ghsTotalError N (ghsHeight N) (ghsScaleCount N) σ
      ≤ (N : ℝ) * (ghsErrorConst + ghsTopConst + 32 * Real.log 2
          + 96 * Real.log (Real.log N)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : (65536 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hlogL : (0 : ℝ) ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  have hE0 := ghsErrorConst_nonneg
  have hT0 : (0 : ℝ) ≤ ghsTopConst := by
    rw [ghsTopConst]
    have hC := mertensBlockGapConst_nonneg
    have h1 : (0 : ℝ) ≤ Real.log 4096 := Real.log_nonneg (by norm_num)
    have h2 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hnum : (0 : ℝ) ≤ (Real.log 4096 + mertensBlockGapConst) / Real.log 2 := by positivity
    nlinarith
  rw [ghsTotalError]
  refine max_le ?_ (max_le ?_ ?_)
  · -- the truncation error
    refine le_trans (ghsUniformError_le hlogN (log_pow_le_ghsHeight N) hx) ?_
    have hstep : ghsErrorConst * ((N : ℝ) / Real.log N) ≤ ghsErrorConst * (N : ℝ) := by
      refine mul_le_mul_of_nonneg_left ?_ hE0
      rw [div_le_iff₀ hL0]
      nlinarith [hN0, hlogN]
    refine le_trans hstep ?_
    have : (0 : ℝ) ≤ ghsTopConst + 32 * Real.log 2 + 96 * Real.log (Real.log N) := by
      positivity
    nlinarith [hN0.le, this]
  · -- the small block
    refine le_trans (ghs_small_block_le hlogN (by omega) hroot) ?_
    have : (0 : ℝ) ≤ ghsErrorConst + ghsTopConst := by linarith
    nlinarith [hN0.le, this]
  · -- the top block
    refine le_trans (ghs_top_block_le hN hn2) ?_
    have : (0 : ℝ) ≤ ghsErrorConst + 32 * Real.log 2 + 96 * Real.log (Real.log N) := by
      positivity
    nlinarith [hN0.le, this]

/-- **The total error, multiplied by the number of blocks and divided by `N·log N`, vanishes.** -/
theorem tendsto_ghsTotalError_majorant (C : ℝ) :
    Tendsto (fun N : ℕ =>
        ((ghsScaleCount N + 2 : ℕ) : ℝ) * (C + 96 * Real.log (Real.log N)) / Real.log N)
      atTop (𝓝 0) := by
  have hsplit : ∀ N : ℕ,
      ((ghsScaleCount N + 2 : ℕ) : ℝ) * (C + 96 * Real.log (Real.log N)) / Real.log N
        = C * (((ghsScaleCount N : ℕ) : ℝ) / Real.log N)
          + 2 * C / Real.log N
          + 96 * ((((ghsScaleCount N : ℕ) : ℝ) * Real.log (Real.log N)) / Real.log N)
          + 192 * (Real.log (Real.log N) / Real.log N) := by
    intro N
    push_cast
    ring
  refine Tendsto.congr (fun N => (hsplit N).symm) ?_
  have h1 : Tendsto (fun N : ℕ => C * (((ghsScaleCount N : ℕ) : ℝ) / Real.log N))
      atTop (𝓝 0) := by
    have := tendsto_ghsScaleCount_div_log.const_mul C
    simpa using this
  have h2 : Tendsto (fun N : ℕ => 2 * C / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_natCast_atTop
  have h4 : Tendsto (fun N : ℕ => 192 * (Real.log (Real.log N) / Real.log N))
      atTop (𝓝 0) := by
    have := tendsto_log_log_div_log.const_mul (192 : ℝ)
    simpa using this
  have h3 : Tendsto (fun N : ℕ =>
      96 * ((((ghsScaleCount N : ℕ) : ℝ) * Real.log (Real.log N)) / Real.log N))
      atTop (𝓝 0) := by
    have hmaj : Tendsto (fun N : ℕ =>
        (96 / Real.log 2) * ((Real.log (Real.log N)) ^ 2 / Real.log N)) atTop (𝓝 0) := by
      have := tendsto_sq_log_log_div_log.const_mul (96 / Real.log 2)
      simpa using this
    refine squeeze_zero' ?_ ?_ hmaj
    · filter_upwards [Filter.eventually_ge_atTop 16] with N hN16
      have hN16R : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN16
      have hL : (0 : ℝ) < Real.log N := Real.log_pos (by linarith)
      have hll : (0 : ℝ) ≤ Real.log (Real.log N) := by
        refine Real.log_nonneg ?_
        have h16 : Real.log 16 ≤ Real.log N := Real.log_le_log (by norm_num) hN16R
        have heq : Real.log 16 = 4 * Real.log 2 := by
          rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
          push_cast; ring
        have hd := Real.log_two_gt_d9
        linarith
      positivity
    · filter_upwards [Filter.eventually_ge_atTop 16] with N hN16
      have hN16R : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN16
      have hL : (0 : ℝ) < Real.log N := Real.log_pos (by linarith)
      have hll : (0 : ℝ) ≤ Real.log (Real.log N) := by
        refine Real.log_nonneg ?_
        have h16 : Real.log 16 ≤ Real.log N := Real.log_le_log (by norm_num) hN16R
        have heq : Real.log 16 = 4 * Real.log 2 := by
          rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
          push_cast; ring
        have hd := Real.log_two_gt_d9
        linarith
      have hK := ghsScaleCount_le hN16
      have hstep : ((ghsScaleCount N : ℕ) : ℝ) * Real.log (Real.log N)
          ≤ (Real.log (Real.log N) / Real.log 2) * Real.log (Real.log N) :=
        mul_le_mul_of_nonneg_right hK hll
      have heq : (Real.log (Real.log N) / Real.log 2) * Real.log (Real.log N)
          = (1 / Real.log 2) * (Real.log (Real.log N)) ^ 2 := by ring
      rw [heq] at hstep
      have hdiv : (((ghsScaleCount N : ℕ) : ℝ) * Real.log (Real.log N)) / Real.log N
          ≤ ((1 / Real.log 2) * (Real.log (Real.log N)) ^ 2) / Real.log N :=
        div_le_div_of_nonneg_right hstep hL.le
      have hval : 96 * (((1 / Real.log 2) * (Real.log (Real.log N)) ^ 2) / Real.log N)
          = (96 / Real.log 2) * ((Real.log (Real.log N)) ^ 2 / Real.log N) := by ring
      nlinarith [hdiv, hval.le, hval.ge]
  have := ((h1.add h2).add h3).add h4
  simpa using this

end RHTower.Sieve

end
