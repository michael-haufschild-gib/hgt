import GaloisForLFunctions.RHTower.Sieve.PolylogLimits
import GaloisForLFunctions.RHTower.Sieve.RelMoebiusSharp

/-!
# The rate of the Möbius majorant under the substitution

The relative twisted Möbius majorant at the substituted cutoff decays faster than any power of the
logarithm, because the cutoff itself is a power of `x`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- A fixed power of the logarithm is dominated by any larger power of a fixed fraction of it. -/
theorem eventually_log_rpow_le_scaled {a C : ℝ} (ha : (1 : ℝ) / 40 < a) (ha1 : a ≤ 1)
    (hC : 0 < C) :
    ∀ᶠ x : ℝ in atTop,
      (Real.log x) ^ ((1 : ℝ) / 40) ≤ C * (Real.log x / 5) ^ a := by
  have hneg : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 40 - a)) atTop (𝓝 0) :=
    tendsto_rpow_log_of_neg (by linarith)
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (show (0 : ℝ) < C / 5 by positivity) hneg] with x hx1 hsmall
  have hu : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hua : (0 : ℝ) < (Real.log x) ^ a := Real.rpow_pos_of_pos hu a
  have h5pos : (0 : ℝ) < (5 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  have h5a : (5 : ℝ) ^ a ≤ 5 := by
    calc (5 : ℝ) ^ a ≤ (5 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) ha1
      _ = 5 := Real.rpow_one 5
  have hdiv : (Real.log x / 5) ^ a = (Real.log x) ^ a / (5 : ℝ) ^ a :=
    Real.div_rpow hu.le (by norm_num : (0:ℝ) ≤ 5) a
  rw [hdiv]
  have hsplit : (Real.log x) ^ ((1 : ℝ) / 40)
      = (Real.log x) ^ ((1 : ℝ) / 40 - a) * (Real.log x) ^ a := by
    rw [← Real.rpow_add hu]
    ring_nf
  have hle1 : (Real.log x) ^ ((1 : ℝ) / 40) ≤ C / 5 * (Real.log x) ^ a := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hsmall hua.le
  have hle2 : C / 5 * (Real.log x) ^ a ≤ C * ((Real.log x) ^ a / (5 : ℝ) ^ a) := by
    have h1 : (Real.log x) ^ a / 5 ≤ (Real.log x) ^ a / (5 : ℝ) ^ a :=
      div_le_div_of_nonneg_left hua.le h5pos h5a
    have h2 : C / 5 * (Real.log x) ^ a = C * ((Real.log x) ^ a / 5) := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 hC.le
  linarith

/-- **The Möbius majorant at the substituted cutoff decays stretched-exponentially.** -/
theorem eventually_budgetS_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop,
      budgetS β x ≤ 3 * Real.exp (-((Real.log x) ^ ((1 : ℝ) / 40))) := by
  have hzf := zeroFreeConst_pos
  filter_upwards [eventually_gallagherCut_ge_exp hβ0 hβ1, Filter.eventually_gt_atTop (1 : ℝ),
    eventually_log_rpow_le_scaled (a := (1 : ℝ) / 10) (C := zeroFreeConst / 16384)
      (by norm_num) (by norm_num) (by positivity),
    eventually_log_rpow_le_scaled (a := (1 : ℝ) / 20) (C := 1) (by norm_num) (by norm_num)
      (by norm_num),
    eventually_log_rpow_le_scaled (a := (1 : ℝ)) (C := 1) (by norm_num) (by norm_num)
      (by norm_num)] with x hNmin hx1 hs1 hs2 hs3
  have hu : (0 : ℝ) < Real.log x := Real.log_pos hx1
  set M : ℝ := Real.exp (Real.log x / 5) with hM
  have hlogM : Real.log M = Real.log x / 5 := Real.log_exp _
  have hM1 : (1 : ℝ) ≤ M := Real.one_le_exp (by positivity)
  have hanti : relMoebiusSharp (budgetNmin β x) ≤ relMoebiusSharp M :=
    relMoebiusSharp_antitone hM1 hNmin
  have hlog0 : (0 : ℝ) ≤ Real.log M := by rw [hlogM]; positivity
  -- the three summands
  have hsq : ((Real.log M) ^ ((1 : ℝ) / 20)) ^ 2 = (Real.log M) ^ ((1 : ℝ) / 10) := by
    rw [← Real.rpow_natCast ((Real.log M) ^ ((1 : ℝ) / 20)) 2, ← Real.rpow_mul hlog0]
    norm_num
  have hT1 : 3 * Real.exp (-(zeroFreeConst / 8192 * ((Real.log M) ^ ((1 : ℝ) / 20)) ^ 2 / 2))
        / Real.pi
      ≤ Real.exp (-((Real.log x) ^ ((1 : ℝ) / 40))) := by
    rw [hsq, hlogM]
    have hexp : Real.exp (-(zeroFreeConst / 8192 * (Real.log x / 5) ^ ((1 : ℝ) / 10) / 2))
        ≤ Real.exp (-((Real.log x) ^ ((1 : ℝ) / 40))) := by
      refine Real.exp_le_exp.2 ?_
      have : zeroFreeConst / 16384 * (Real.log x / 5) ^ ((1 : ℝ) / 10)
          = zeroFreeConst / 8192 * (Real.log x / 5) ^ ((1 : ℝ) / 10) / 2 := by ring
      linarith [hs1, this]
    have hpi3 : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
    have hpos : (0 : ℝ) < Real.exp (-(zeroFreeConst / 8192
        * (Real.log x / 5) ^ ((1 : ℝ) / 10) / 2)) := Real.exp_pos _
    have hstep : 3 * Real.exp (-(zeroFreeConst / 8192
          * (Real.log x / 5) ^ ((1 : ℝ) / 10) / 2)) / Real.pi
        ≤ Real.exp (-(zeroFreeConst / 8192 * (Real.log x / 5) ^ ((1 : ℝ) / 10) / 2)) := by
      rw [div_le_iff₀ Real.pi_pos]
      nlinarith [hpos, hpi3]
    linarith [hstep, hexp]
  have hT2 : 1 / smoothRatio M ≤ Real.exp (-((Real.log x) ^ ((1 : ℝ) / 40))) := by
    rw [smoothRatio, one_div, ← Real.exp_neg, hlogM]
    exact Real.exp_le_exp.2 (by linarith [hs2])
  have hT3 : 1 / M ≤ Real.exp (-((Real.log x) ^ ((1 : ℝ) / 40))) := by
    rw [hM, one_div, ← Real.exp_neg]
    refine Real.exp_le_exp.2 ?_
    have : (Real.log x / 5) ^ (1 : ℝ) = Real.log x / 5 := Real.rpow_one _
    linarith [hs3, this]
  have hexpand : relMoebiusSharp M
      = 3 * Real.exp (-(zeroFreeConst / 8192 * ((Real.log M) ^ ((1 : ℝ) / 20)) ^ 2 / 2))
          / Real.pi + 1 / smoothRatio M + 1 / M := rfl
  rw [budgetS]
  rw [hexpand] at hanti
  linarith [hanti, hT1, hT2, hT3]

/-- **Any power of the logarithm against the Möbius majorant vanishes.** -/
theorem tendsto_rpow_log_mul_budgetS {β c : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun x : ℝ => (Real.log x) ^ c * budgetS β x) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun x : ℝ =>
      3 * ((Real.log x) ^ c * Real.exp (-((Real.log x) ^ ((1 : ℝ) / 40))))) atTop (𝓝 0) := by
    have := tendsto_rpow_log_mul_exp_neg (c := c) (a := (1 : ℝ) / 40) (by norm_num)
    simpa using this.const_mul (3 : ℝ)
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      eventually_gallagherCut_ge_exp hβ0 hβ1] with x hx1 hNmin
    have hu : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hM1 : (1 : ℝ) ≤ Real.exp (Real.log x / 5) := Real.one_le_exp (by positivity)
    have hN : (0 : ℝ) < budgetNmin β x := lt_of_lt_of_le (by linarith) hNmin
    have := relMoebiusSharp_nonneg hN
    have hpow : (0 : ℝ) ≤ (Real.log x) ^ c := Real.rpow_nonneg hu.le c
    rw [budgetS]
    exact mul_nonneg hpow this
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), eventually_budgetS_le hβ0 hβ1]
      with x hx1 hS
    have hu : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hpow : (0 : ℝ) ≤ (Real.log x) ^ c := Real.rpow_nonneg hu.le c
    calc (Real.log x) ^ c * budgetS β x
        ≤ (Real.log x) ^ c * (3 * Real.exp (-((Real.log x) ^ ((1 : ℝ) / 40)))) :=
          mul_le_mul_of_nonneg_left hS hpow
      _ = 3 * ((Real.log x) ^ c * Real.exp (-((Real.log x) ^ ((1 : ℝ) / 40)))) := by ring

end

end RHTower.Sieve
