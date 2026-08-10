import GaloisForLFunctions.RHTower.Sieve.GhsSmallBlockBound

/-!
# The last scale is bounded

The number of scales is `K = Nat.log 2 ⌊(log N)/(4 log 2)⌋`, so `2^K` is within a factor two of
`(log N)/(4 log 2)` — `Nat.lt_pow_succ_log_self` gives the lower bound the threshold does not.
Consequently the exponent `1/2^K` is `≍ (log 2)/log N` and

```text
ghsScale N K = ⌊N^{1/2^K}⌋ ≤ exp((32 log 2)/3) ≤ 2^{11} = 2048 ,
```

an absolute constant.  So the last geometric endpoint `ghsBlockLeft N K = ⌊N/ghsScale N K⌋` is at
least `N/2048`: the geometric partition stops a bounded factor below `N`, which is exactly what
makes the top block's trivial bound cost only `O(N)`.
-/

noncomputable section

namespace RHTower.Sieve

open Complex Filter Asymptotics Finset Topology

/-- **The last scale is at most `2048`.** -/
theorem ghsScale_scaleCount_le {N : ℕ} (hN : 65536 ≤ N) :
    ghsScale N (ghsScaleCount N) ≤ 2048 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hNR : (65536 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  set L : ℝ := Real.log N with hLdef
  -- `log N ≥ 16 log 2`
  have hL16 : 16 * Real.log 2 ≤ L := by
    have hpow : Real.log ((65536 : ℝ)) ≤ L := Real.log_le_log (by norm_num) hNR
    have heq : Real.log ((65536 : ℝ)) = 16 * Real.log 2 := by
      rw [show (65536 : ℝ) = 2 ^ (16 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    linarith [hpow, heq.le, heq.ge]
  have hL0 : (0 : ℝ) < L := by linarith
  set m : ℕ := ⌊L / (4 * Real.log 2)⌋₊ with hmdef
  have hratio4 : (4 : ℝ) ≤ L / (4 * Real.log 2) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hm4 : 4 ≤ m := Nat.le_floor (by exact_mod_cast hratio4)
  have hmR : (L / (4 * Real.log 2)) - 1 < (m : ℝ) := by
    rw [hmdef]
    linarith [Nat.lt_floor_add_one (L / (4 * Real.log 2))]
  -- `2^K` is at least `3L/(32 log 2)`
  have hlt : m < 2 ^ (ghsScaleCount N + 1) := by
    rw [ghsScaleCount, ← hmdef]
    exact Nat.lt_pow_succ_log_self (by norm_num) m
  have hltR : (m : ℝ) < 2 * (2 : ℝ) ^ ghsScaleCount N := by
    have hc : ((m : ℕ) : ℝ) < ((2 ^ (ghsScaleCount N + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
    push_cast at hc
    rw [pow_succ] at hc
    linarith [hc]
  have hpowlow : 3 * L / (32 * Real.log 2) < (2 : ℝ) ^ ghsScaleCount N := by
    have h1 : (3 / 4 : ℝ) * (L / (4 * Real.log 2)) ≤ L / (4 * Real.log 2) - 1 := by
      linarith [hratio4]
    have h2 : (3 / 4 : ℝ) * (L / (4 * Real.log 2)) < (m : ℝ) := by linarith
    have h3 : (3 / 8 : ℝ) * (L / (4 * Real.log 2)) < (2 : ℝ) ^ ghsScaleCount N := by
      linarith [hltR, h2]
    have heq : (3 / 8 : ℝ) * (L / (4 * Real.log 2)) = 3 * L / (32 * Real.log 2) := by
      field_simp; ring
    linarith [h3, heq.le, heq.ge]
  have hpow0 : (0 : ℝ) < (2 : ℝ) ^ ghsScaleCount N := by positivity
  -- the exponent is small
  have hkey : 3 * L < (2 : ℝ) ^ ghsScaleCount N * (32 * Real.log 2) :=
    (div_lt_iff₀ (by positivity)).1 hpowlow
  have hexp : L / (2 : ℝ) ^ ghsScaleCount N ≤ 32 * Real.log 2 / 3 := by
    rw [div_le_div_iff₀ hpow0 (by norm_num)]
    linarith [hkey]
  -- the scale is bounded
  have hrw : (N : ℝ) ^ ((1 : ℝ) / 2 ^ ghsScaleCount N)
      = Real.exp ((1 / 2 ^ ghsScaleCount N) * L) := by
    rw [Real.rpow_def_of_pos hN0, mul_comm]
  have hval : (N : ℝ) ^ ((1 : ℝ) / 2 ^ ghsScaleCount N) ≤ 2048 := by
    rw [hrw]
    have hle : (1 / (2 : ℝ) ^ ghsScaleCount N) * L ≤ 11 * Real.log 2 := by
      have : L / (2 : ℝ) ^ ghsScaleCount N = (1 / (2 : ℝ) ^ ghsScaleCount N) * L := by ring
      rw [← this]
      linarith [hexp, hlog2]
    calc Real.exp ((1 / 2 ^ ghsScaleCount N) * L) ≤ Real.exp (11 * Real.log 2) :=
          Real.exp_le_exp.2 hle
      _ = 2048 := by
          rw [show (11 : ℝ) * Real.log 2 = Real.log (2 ^ (11 : ℕ)) by
            rw [Real.log_pow]; push_cast; ring]
          rw [Real.exp_log (by norm_num)]
          norm_num
  rw [ghsScale]
  calc ⌊(N : ℝ) ^ ((1 : ℝ) / 2 ^ ghsScaleCount N)⌋₊ ≤ ⌊(2048 : ℝ)⌋₊ := Nat.floor_le_floor hval
    _ = 2048 := by norm_num

/-- The last geometric endpoint is at least `N/2048`. -/
theorem ghsBlockLeft_scaleCount_ge {N : ℕ} (hN : 65536 ≤ N) :
    N / 2048 ≤ ghsBlockLeft N (ghsScaleCount N) := by
  rw [ghsBlockLeft]
  exact Nat.div_le_div_left (ghsScale_scaleCount_le hN) (one_le_ghsScale (by omega))

end RHTower.Sieve

end
