import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIBlockBudget
import GaloisForLFunctions.RHTower.Sieve.MenonPrimeTwistRangeReverseAbel
import GaloisForLFunctions.RHTower.BurnolPrimeLogSummability

/-!
# Menon harmonic Case II: the logarithmic-power threshold

For a harmonic prime block `(a, Y]` with `a < Y ≤ 2a`, the Case-II argument bounds the block
polynomial by `(B + E + P) / (log(a + 1) · (a + 1))`, where `B` is the Perron budget
`menonHarmonicCaseIIBudget`, `E` the cost of the two smoothing transition windows and `P` the
proper-prime-power von Mangoldt mass on `(a, Y]`. This module shows that this threshold is
eventually at most `(budget constant + 24) / (log a)^20`, using `(log a)^20 ≤ √a` for large `a` and
the bound `P ≤ 2 √Y log Y`.

## Main results

- `eventually_menonHarmonicCaseII_threshold_le`: for every `C0 ≥ 0`, for all sufficiently large `a`
  and all `Y` with `a < Y ≤ 2a`, the Case-II threshold is at most
  `menonHarmonicCaseIIThresholdConstant C0 / (log a)^20`.

## Hypotheses

Unconditional. The only assumptions are `0 ≤ C0` and the block range `a < Y ≤ 2a`.
-/

namespace RHTower.Sieve

open Filter Finset ArithmeticFunction

noncomputable section

/-- Threshold constant `menonHarmonicCaseIIBudgetConstant C0 + 24` of the Case-II block bound. -/
def menonHarmonicCaseIIThresholdConstant (C0 : ℝ) : ℝ :=
  menonHarmonicCaseIIBudgetConstant C0 + 24

theorem menonHarmonicCaseIIThresholdConstant_nonneg {C0 : ℝ} (hC0 : 0 ≤ C0) :
    0 ≤ menonHarmonicCaseIIThresholdConstant C0 := by
  rw [menonHarmonicCaseIIThresholdConstant, menonHarmonicCaseIIBudgetConstant,
    menonHarmonicCaseIIKernelConstant, menonHarmonicCaseIIFixedPolylogConstant]
  positivity

private theorem primePowerDefectIoc_le_full (a Y : ℕ) :
    primePowerDefectIoc a Y ≤ primePowerDefect Y := by
  rw [primePowerDefect]
  unfold primePowerDefectIoc
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact Finset.mem_range.2 (by
      have := (Finset.mem_Ioc.mp hn).2
      omega)
  · intro n _hn _hna
    by_cases hp : n.Prime
    · rw [if_pos hp, vonMangoldt_apply_prime hp, sub_self]
    · rw [if_neg hp, sub_zero]
      exact vonMangoldt_nonneg

/-- Assuming `0 ≤ C0`: eventually in `a`, for all `Y` with `a < Y ≤ 2a`,
`((B + E + P) / log(a + 1)) / (a + 1) ≤ menonHarmonicCaseIIThresholdConstant C0 / (log a)^20`, where
`B` is the Case-II budget, `E` the transition-window envelope and `P` the prime-power defect on `(a, Y]`. -/
theorem eventually_menonHarmonicCaseII_threshold_le (C0 : ℝ) (hC0 : 0 ≤ C0) :
    ∀ᶠ a : ℕ in atTop, ∀ {Y : ℕ}, a < Y → Y ≤ 2 * a →
      (((menonHarmonicCaseIIBudget C0 a Y +
              menonWideIntervalTransitionEnvelope (4 * Y)
                (menonHarmonicCaseIISmoothingWidth a)) +
            primePowerDefectIoc a Y) /
          Real.log ((a + 1 : ℕ) : ℝ)) /
        ((a + 1 : ℕ) : ℝ) ≤
      menonHarmonicCaseIIThresholdConstant C0 /
        (Real.log (a : ℝ)) ^ (20 : ℕ) := by
  have hpow := burnolEventually_log_pow_le_rpow (δ := (1 : ℝ) / 2) (by norm_num) 20
  have hpowNat : ∀ᶠ a : ℕ in atTop,
      Real.log (a : ℝ) ^ 20 ≤ Real.sqrt (a : ℝ) := by
    have hcomp := tendsto_natCast_atTop_atTop.eventually hpow
    filter_upwards [hcomp, eventually_ge_atTop (1 : ℕ)] with a ha ha1
    rw [show (a : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (a : ℝ) by
      rw [Real.sqrt_eq_rpow]] at ha
    exact ha
  filter_upwards [hpowNat, eventually_ge_atTop (256 : ℕ)] with a hpow ha256
  intro Y haY hYa
  let la : ℝ := Real.log (a : ℝ)
  let lap : ℝ := Real.log ((a + 1 : ℕ) : ℝ)
  let d : ℝ := lap * ((a + 1 : ℕ) : ℝ)
  have ha1 : (1 : ℝ) < (a : ℝ) := by exact_mod_cast (show 1 < a by omega)
  have halog : 1 ≤ la := by
    dsimp only [la]
    have h256log : (1 : ℝ) ≤ Real.log 256 := by
      have h256exp : Real.exp 1 < 256 := Real.exp_one_lt_d9.trans (by norm_num)
      exact (Real.le_log_iff_exp_le (by norm_num)).2 h256exp.le
    exact h256log.trans (Real.log_le_log (by norm_num) (by exact_mod_cast ha256))
  have hla0 : 0 < la := zero_lt_one.trans_le halog
  have hlap : la ≤ lap := by
    dsimp only [la, lap]
    exact Real.log_le_log (by positivity) (by exact_mod_cast (Nat.le_succ a))
  have hlap1 : 1 ≤ lap := halog.trans hlap
  have hd0 : 0 < d := by dsimp only [d]; positivity
  have hbud0 : 0 ≤ menonHarmonicCaseIIBudgetConstant C0 := by
    rw [menonHarmonicCaseIIBudgetConstant, menonHarmonicCaseIIKernelConstant,
      menonHarmonicCaseIIFixedPolylogConstant]
    positivity
  have hbudget := menonHarmonicCaseIIBudget_le hC0 (show 64 ≤ a by omega)
    (by simpa only [la] using halog)
    haY hYa
  have hbudgetQ : menonHarmonicCaseIIBudget C0 a Y / d ≤
      menonHarmonicCaseIIBudgetConstant C0 / la ^ 20 := by
    calc
      menonHarmonicCaseIIBudget C0 a Y / d ≤
          (menonHarmonicCaseIIBudgetConstant C0 * (a : ℝ) / la ^ 20) / d :=
        div_le_div_of_nonneg_right hbudget hd0.le
      _ ≤ menonHarmonicCaseIIBudgetConstant C0 / la ^ 20 := by
        rw [div_div]
        have hden : (1 : ℝ) ≤ d := by
          dsimp only [d]
          have : (1 : ℝ) ≤ ((a + 1 : ℕ) : ℝ) := by
            exact_mod_cast (show 1 ≤ a + 1 by omega)
          nlinarith
        have haad : (a : ℝ) ≤ d := by
          dsimp only [d]
          have haa : (a : ℝ) ≤ ((a + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ a
          nlinarith
        calc
          menonHarmonicCaseIIBudgetConstant C0 * (a : ℝ) / (la ^ 20 * d) =
              (menonHarmonicCaseIIBudgetConstant C0 / la ^ 20) * ((a : ℝ) / d) := by ring
          _ ≤ (menonHarmonicCaseIIBudgetConstant C0 / la ^ 20) * 1 := by
            gcongr
            exact (div_le_one hd0).2 haad
          _ = menonHarmonicCaseIIBudgetConstant C0 / la ^ 20 := by ring
  have hlog8 : Real.log ((4 * Y : ℕ) : ℝ) ≤ 4 * la := by
    have h4Y : ((4 * Y : ℕ) : ℝ) ≤ 8 * (a : ℝ) := by exact_mod_cast (by omega : 4 * Y ≤ 8 * a)
    have hY0 : 0 < Y := by omega
    have hlogle := Real.log_le_log (by exact_mod_cast (show 0 < 4 * Y by omega)) h4Y
    have hlog8a : Real.log (8 * (a : ℝ)) = Real.log 8 + la := by
      rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt (by positivity : (0 : ℝ) < (a : ℝ)))]
    have hlog8const : Real.log (8 : ℝ) ≤ 3 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hlog2 ⊢
      linarith
    rw [hlog8a] at hlogle
    nlinarith
  have hsqrtLe : Real.sqrt (a : ℝ) ≤ (a : ℝ) := by
    have hs0 := Real.sqrt_nonneg (a : ℝ)
    have hsSq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (a : ℝ))
    nlinarith [show (1 : ℝ) ≤ (a : ℝ) by exact_mod_cast (show 1 ≤ a by omega)]
  have hpowA : la ^ 20 ≤ (a : ℝ) := hpow.trans hsqrtLe
  have htransitionQ :
      menonWideIntervalTransitionEnvelope (4 * Y)
          (menonHarmonicCaseIISmoothingWidth a) / d ≤ 16 / la ^ 20 := by
    rw [menonWideIntervalTransitionEnvelope, menonHarmonicCaseIISmoothingWidth]
    have hH0 : 0 ≤ (a : ℝ) / la ^ 20 := by positivity
    have hlog0 : 0 ≤ Real.log ((4 * Y : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 4 * Y by omega))
    have hnum : 2 * ((a : ℝ) / la ^ 20 + 1) *
          Real.log ((4 * Y : ℕ) : ℝ) ≤
        8 * ((a : ℝ) / la ^ 20 + 1) * la := by
      nlinarith [mul_le_mul_of_nonneg_left hlog8 (by positivity : 0 ≤ 2 * ((a : ℝ) / la ^ 20 + 1))]
    calc
      2 * ((a : ℝ) / la ^ 20 + 1) * Real.log ((4 * Y : ℕ) : ℝ) / d ≤
          (8 * ((a : ℝ) / la ^ 20 + 1) * la) / d :=
        div_le_div_of_nonneg_right hnum hd0.le
      _ ≤ 8 * ((a : ℝ) / la ^ 20 + 1) / ((a + 1 : ℕ) : ℝ) := by
        dsimp only [d]
        have hsucc0 : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := by positivity
        have hfac0 : 0 ≤ 8 * ((a : ℝ) / la ^ 20 + 1) := by positivity
        rw [div_le_div_iff₀ (by simpa only [d] using hd0) hsucc0]
        have hmul := mul_le_mul_of_nonneg_left hlap hfac0
        nlinarith
      _ ≤ 16 / la ^ 20 := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < ((a + 1 : ℕ) : ℝ)) (pow_pos hla0 20)]
        have haa : (a : ℝ) + 1 = ((a + 1 : ℕ) : ℝ) := by push_cast; ring
        rw [← haa]
        field_simp [ne_of_gt hla0]
        nlinarith
  have hdefect : primePowerDefectIoc a Y ≤ 8 * Real.sqrt (a : ℝ) * la := by
    have hfull := (primePowerDefectIoc_le_full a Y).trans
      (primePowerDefect_le (show 1 ≤ Y by omega))
    have hsqrt : Real.sqrt (Y : ℝ) ≤ 2 * Real.sqrt (a : ℝ) := by
      have hYaR : (Y : ℝ) ≤ 2 * (a : ℝ) := by exact_mod_cast hYa
      have hs := Real.sqrt_le_sqrt hYaR
      have htwo : Real.sqrt (2 * (a : ℝ)) ≤ 2 * Real.sqrt (a : ℝ) := by
        have hs0 := Real.sqrt_nonneg (a : ℝ)
        have hsqrt2 : Real.sqrt (2 : ℝ) ≤ 2 := by
          have hsq2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
          have hs20 := Real.sqrt_nonneg (2 : ℝ)
          nlinarith
        rw [Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num)]
        exact mul_le_mul_of_nonneg_right hsqrt2 hs0
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs.trans htwo
    have hlogY : Real.log (Y : ℝ) ≤ 2 * la := by
      have hY2a : (Y : ℝ) ≤ 2 * (a : ℝ) := by exact_mod_cast hYa
      have hY0 : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast (show 0 < Y by omega)
      have hlogle := Real.log_le_log hY0 hY2a
      have hlog2a : Real.log (2 * (a : ℝ)) = Real.log 2 + la := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (by positivity : (0 : ℝ) < (a : ℝ)))]
      have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at h
        exact h
      rw [hlog2a] at hlogle
      nlinarith
    have hlogY0 : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y by omega))
    calc
      primePowerDefectIoc a Y ≤ 2 * Real.sqrt (Y : ℝ) * Real.log (Y : ℝ) := hfull
      _ ≤ 2 * (2 * Real.sqrt (a : ℝ)) * (2 * la) := by gcongr
      _ = 8 * Real.sqrt (a : ℝ) * la := by ring
  have hsqrta0 : 0 < Real.sqrt (a : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hdefectQ : primePowerDefectIoc a Y / d ≤ 8 / la ^ 20 := by
    calc
      primePowerDefectIoc a Y / d ≤ (8 * Real.sqrt (a : ℝ) * la) / d :=
        div_le_div_of_nonneg_right hdefect hd0.le
      _ ≤ 8 / Real.sqrt (a : ℝ) := by
        dsimp only [d]
        rw [div_le_div_iff₀ hd0 hsqrta0]
        have hsqa : Real.sqrt (a : ℝ) * Real.sqrt (a : ℝ) = (a : ℝ) :=
          Real.mul_self_sqrt (by positivity)
        have haa : (a : ℝ) ≤ ((a + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ a
        nlinarith [hlap, hsqa]
      _ ≤ 8 / la ^ 20 := by
        exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hla0 20) hpow
  have hrearrange :
      (((menonHarmonicCaseIIBudget C0 a Y +
              menonWideIntervalTransitionEnvelope (4 * Y)
                (menonHarmonicCaseIISmoothingWidth a)) +
            primePowerDefectIoc a Y) / lap) /
          ((a + 1 : ℕ) : ℝ) =
        menonHarmonicCaseIIBudget C0 a Y / d +
          menonWideIntervalTransitionEnvelope (4 * Y)
            (menonHarmonicCaseIISmoothingWidth a) / d +
          primePowerDefectIoc a Y / d := by
    dsimp only [d]
    ring
  rw [show Real.log ((a + 1 : ℕ) : ℝ) = lap by rfl, hrearrange,
    menonHarmonicCaseIIThresholdConstant]
  have hsplit :
      (menonHarmonicCaseIIBudgetConstant C0 + 24) / la ^ 20 =
        menonHarmonicCaseIIBudgetConstant C0 / la ^ 20 +
          16 / la ^ 20 + 8 / la ^ 20 := by ring
  rw [hsplit]
  linarith

end

end RHTower.Sieve
