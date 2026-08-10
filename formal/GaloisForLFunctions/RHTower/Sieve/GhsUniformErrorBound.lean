import GaloisForLFunctions.RHTower.Sieve.GhsSizeBounds

/-!
# The truncation error is `N/log N`

At the height `ghsHeight N ≥ (log N)⁶` the uniform Perron error collapses:

```text
ghsUniformError N n σ = ((3 log N)⁴/(log 2)³)·(N+½)^σ·(5(1 + 3 log N) + 4(1 + log N))/(π n)
                      ≤ 81(log N)⁴/(log 2)³ · 3N · 22 log N / (π (log N)⁶)
                      = ghsErrorConst · N/log N ,
```

so `K` of them, divided by `N·log N`, is `ghsErrorConst·K/(log N)²`, and `K ≤ (log log N)/log 2`.

The abscissa enters only through `(N+½)^σ`, which is why the bound is stated with the hypothesis
`(N+½)^σ ≤ 3N` — satisfied by `σ = 1 + 1/log N`, and by any `σ = 1 + 1/log z` with `z ≥ N`.
-/

noncomputable section

namespace RHTower.Sieve

open Complex Filter Asymptotics Finset Topology

/-- The constant of the truncation error. -/
def ghsErrorConst : ℝ := 5346 / ((Real.log 2) ^ 3 * Real.pi)

theorem ghsErrorConst_nonneg : 0 ≤ ghsErrorConst := by
  rw [ghsErrorConst]
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpi := Real.pi_pos
  positivity

/-- **The uniform truncation error is `N/log N`.** -/
theorem ghsUniformError_le {N n : ℕ} {σ : ℝ} (hlogN : (3 : ℝ) ≤ Real.log N)
    (hn : (Real.log N) ^ 6 ≤ (n : ℝ)) (hx : ((N : ℝ) + 1 / 2) ^ σ ≤ 3 * (N : ℝ)) :
    ghsUniformError N n σ ≤ ghsErrorConst * ((N : ℝ) / Real.log N) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpi := Real.pi_pos
  set L : ℝ := Real.log N with hLdef
  have hL : (3 : ℝ) ≤ L := hlogN
  have hL0 : (0 : ℝ) < L := by linarith
  have hL6 : (0 : ℝ) < L ^ 6 := by positivity
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith [hn, hL6]
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hxσ : (0 : ℝ) ≤ ((N : ℝ) + 1 / 2) ^ σ := Real.rpow_nonneg (by linarith) σ
  -- the three factors
  have hf1 : (3 * L) ^ 4 / (Real.log 2) ^ 3 = 81 * L ^ 4 / (Real.log 2) ^ 3 := by ring_nf
  have hf3 : 5 * (1 + 3 * L) + 4 * (1 + L) ≤ 22 * L := by linarith
  have hf30 : (0 : ℝ) ≤ 5 * (1 + 3 * L) + 4 * (1 + L) := by linarith
  -- numerator
  have hnum : ((3 * L) ^ 4 / (Real.log 2) ^ 3) * ((N : ℝ) + 1 / 2) ^ σ
        * (5 * (1 + 3 * L) + 4 * (1 + L))
      ≤ (81 * L ^ 4 / (Real.log 2) ^ 3) * (3 * (N : ℝ)) * (22 * L) := by
    rw [hf1]
    have hA0 : (0 : ℝ) ≤ 81 * L ^ 4 / (Real.log 2) ^ 3 := by positivity
    have hstep1 : (81 * L ^ 4 / (Real.log 2) ^ 3) * ((N : ℝ) + 1 / 2) ^ σ
        ≤ (81 * L ^ 4 / (Real.log 2) ^ 3) * (3 * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hx hA0
    have hB0 : (0 : ℝ) ≤ (81 * L ^ 4 / (Real.log 2) ^ 3) * (3 * (N : ℝ)) := by positivity
    calc (81 * L ^ 4 / (Real.log 2) ^ 3) * ((N : ℝ) + 1 / 2) ^ σ
          * (5 * (1 + 3 * L) + 4 * (1 + L))
        ≤ ((81 * L ^ 4 / (Real.log 2) ^ 3) * (3 * (N : ℝ)))
            * (5 * (1 + 3 * L) + 4 * (1 + L)) :=
          mul_le_mul_of_nonneg_right hstep1 hf30
      _ ≤ ((81 * L ^ 4 / (Real.log 2) ^ 3) * (3 * (N : ℝ))) * (22 * L) :=
          mul_le_mul_of_nonneg_left hf3 hB0
  -- denominator
  have hden : Real.pi * (L ^ 6) ≤ Real.pi * ((n : ℝ) * 2 ^ (0 : ℕ)) := by
    have hstep : (L : ℝ) ^ 6 ≤ (n : ℝ) * 2 ^ (0 : ℕ) := by
      simp only [pow_zero, mul_one]
      exact hn
    exact mul_le_mul_of_nonneg_left hstep hpi.le
  have hden0 : (0 : ℝ) < Real.pi * (L ^ 6) := by positivity
  rw [ghsUniformError, ← hLdef]
  have hquot : ((3 * L) ^ 4 / (Real.log 2) ^ 3) * ((N : ℝ) + 1 / 2) ^ σ
        * (5 * (1 + 3 * L) + 4 * (1 + L)) / (Real.pi * ((n : ℝ) * 2 ^ (0 : ℕ)))
      ≤ ((81 * L ^ 4 / (Real.log 2) ^ 3) * (3 * (N : ℝ)) * (22 * L)) / (Real.pi * (L ^ 6)) := by
    have hn1 : (0 : ℝ) < (n : ℝ) * 2 ^ (0 : ℕ) := by
      simp only [pow_zero, mul_one]
      exact hn0
    have hden1 : (0 : ℝ) < Real.pi * ((n : ℝ) * 2 ^ (0 : ℕ)) := mul_pos hpi hn1
    have hnum'0 : (0 : ℝ) ≤ (81 * L ^ 4 / (Real.log 2) ^ 3) * (3 * (N : ℝ)) * (22 * L) := by
      positivity
    calc ((3 * L) ^ 4 / (Real.log 2) ^ 3) * ((N : ℝ) + 1 / 2) ^ σ
          * (5 * (1 + 3 * L) + 4 * (1 + L)) / (Real.pi * ((n : ℝ) * 2 ^ (0 : ℕ)))
        ≤ ((81 * L ^ 4 / (Real.log 2) ^ 3) * (3 * (N : ℝ)) * (22 * L))
            / (Real.pi * ((n : ℝ) * 2 ^ (0 : ℕ))) :=
          div_le_div_of_nonneg_right hnum hden1.le
      _ ≤ ((81 * L ^ 4 / (Real.log 2) ^ 3) * (3 * (N : ℝ)) * (22 * L)) / (Real.pi * (L ^ 6)) :=
          div_le_div_of_nonneg_left hnum'0 hden0 hden
  refine le_trans hquot (le_of_eq ?_)
  rw [ghsErrorConst]
  field_simp
  ring

/-- The number of scales is `o(log N)`. -/
theorem tendsto_ghsScaleCount_div_log :
    Tendsto (fun N : ℕ => ((ghsScaleCount N : ℕ) : ℝ) / Real.log N) atTop (𝓝 0) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmaj : Tendsto (fun N : ℕ => (1 / Real.log 2) * (Real.log (Real.log N) / Real.log N))
      atTop (𝓝 0) := by
    have := tendsto_log_log_div_log.const_mul (1 / Real.log 2)
    simpa using this
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_ge_atTop 3] with N hN3
    have hN3R : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
    have hlogN : (0 : ℝ) < Real.log N := Real.log_pos (by linarith)
    positivity
  · filter_upwards [Filter.eventually_ge_atTop 16] with N hN16
    have hN16R : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN16
    have hlogN : (0 : ℝ) < Real.log N := Real.log_pos (by linarith)
    have hK := ghsScaleCount_le hN16
    rw [div_le_iff₀ hlogN]
    have hrw : (1 / Real.log 2) * (Real.log (Real.log N) / Real.log N) * Real.log N
        = Real.log (Real.log N) / Real.log 2 := by
      field_simp
    rw [hrw]
    exact hK

end RHTower.Sieve

end
