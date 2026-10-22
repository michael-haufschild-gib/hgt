import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureBoundaryCapacity
import GaloisForLFunctions.RHTower.XiCensusVonMangoldtBridge

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace RHTower

noncomputable section

theorem stripFinsetPos_subset_local {S T : ℝ} (hST : S ≤ T) :
    stripFinsetPos S ⊆ stripFinsetPos T := by
  intro z hz
  rw [mem_stripFinsetPos] at hz ⊢
  exact ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1.trans hST, hz.2.2.2.2⟩

theorem monotone_xiPosCriticalZeroCount_local : Monotone xiPosCriticalZeroCount := by
  intro S T hST
  exact Finset.sum_le_sum_of_subset
    (Finset.filter_subset_filter _ (stripFinsetPos_subset_local hST))

theorem monotone_xiOffLineZeroCount_local : Monotone xiOffLineZeroCount := by
  intro S T hST
  exact Finset.sum_le_sum_of_subset
    (Finset.filter_subset_filter _ (stripFinsetPos_subset_local hST))

theorem xiPosCriticalZeroCount_sub_le_xiPosZeroCount_sub
    {S T : ℝ} (hST : S ≤ T) :
    xiPosCriticalZeroCount T - xiPosCriticalZeroCount S ≤
      xiPosZeroCount T - xiPosZeroCount S := by
  have hcrit := monotone_xiPosCriticalZeroCount_local hST
  have hoff := monotone_xiOffLineZeroCount_local hST
  have hS := xiPosCriticalZeroCount_add_xiOffLineZeroCount S
  have hT := xiPosCriticalZeroCount_add_xiOffLineZeroCount T
  omega

theorem xiPosCriticalZeroCount_cast_le_canonicalZeroCount (n : ℕ) :
    (xiPosCriticalZeroCount (n : ℝ) : ℝ) ≤
      criticalFeatureCanonicalZeroCount n := by
  have hcrit := xiPosCriticalZeroCount_le (n : ℝ)
  have hcount := xiPosZeroCount_eq_xiZeroCount (T := (n : ℝ)) (by positivity)
  have hcritReal : (xiPosCriticalZeroCount (n : ℝ) : ℝ) ≤
      (xiPosZeroCount (n : ℝ) : ℝ) := by exact_mod_cast hcrit
  have hcountReal : (xiPosZeroCount (n : ℝ) : ℝ) =
      criticalFeatureCanonicalZeroCount n := by
    dsimp [criticalFeatureCanonicalZeroCount]
    exact_mod_cast hcount
  rwa [hcountReal] at hcritReal

theorem tendsto_criticalFeatureCanonicalZeroCount_nat_add_natLog_ratio
    (c : ℕ) :
    Tendsto (fun n : ℕ =>
      criticalFeatureCanonicalZeroCount (n + c) /
        ((n : ℝ) * Real.log (n : ℝ))) atTop
      (𝓝 (1 / (2 * Real.pi))) := by
  have hshift : Tendsto (fun n : ℕ => n + c) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with a ha
    omega
  have hmain := tendsto_criticalFeatureCanonicalZeroCount_natLog_ratio.comp hshift
  have hmodel := tendsto_natCast_add_mul_log_div_natCast_mul_log c
  have hprod := hmain.mul hmodel
  have heq : ∀ᶠ n : ℕ in atTop,
      (criticalFeatureCanonicalZeroCount (n + c) /
          (((n + c : ℕ) : ℝ) * Real.log ((n + c : ℕ) : ℝ))) *
        ((((n + c : ℕ) : ℝ) * Real.log ((n + c : ℕ) : ℝ)) /
          ((n : ℝ) * Real.log (n : ℝ))) =
        criticalFeatureCanonicalZeroCount (n + c) /
          ((n : ℝ) * Real.log (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hlogn : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hn)).ne'
    have hnc0 : ((n + c : ℕ) : ℝ) ≠ 0 := by positivity
    have hlognc : Real.log ((n + c : ℕ) : ℝ) ≠ 0 := by
      apply (Real.log_pos ?_).ne'
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) (le_add_right hn))
    field_simp
  have h := hprod.congr' heq
  simpa only [mul_one] using h

theorem tendsto_criticalFeatureCanonicalZeroCount_nat_add_div (c : ℕ) :
    Tendsto (fun n : ℕ =>
      criticalFeatureCanonicalZeroCount (n + c) /
        criticalFeatureCanonicalZeroCount n) atTop (𝓝 1) := by
  have hquot :=
    (tendsto_criticalFeatureCanonicalZeroCount_nat_add_natLog_ratio c).div
      tendsto_criticalFeatureCanonicalZeroCount_natLog_ratio
      (by positivity : (1 / (2 * Real.pi) : ℝ) ≠ 0)
  have heq : ∀ᶠ n : ℕ in atTop,
      (criticalFeatureCanonicalZeroCount (n + c) /
          ((n : ℝ) * Real.log (n : ℝ))) /
        (criticalFeatureCanonicalZeroCount n /
          ((n : ℝ) * Real.log (n : ℝ))) =
      criticalFeatureCanonicalZeroCount (n + c) /
        criticalFeatureCanonicalZeroCount n := by
    filter_upwards [eventually_ge_atTop 2,
      eventually_criticalFeatureCanonicalZeroCount_pos] with n hn hN
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hlogn : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hn)).ne'
    have hN0 : criticalFeatureCanonicalZeroCount n ≠ 0 := ne_of_gt hN
    field_simp
  have ha : (1 / (2 * Real.pi) : ℝ) ≠ 0 := by positivity
  rw [div_self ha] at hquot
  exact hquot.congr' heq

theorem tendsto_criticalFeatureCanonicalZeroCount_nat_add_sub_div_zero
    (c : ℕ) :
    Tendsto (fun n : ℕ =>
      (criticalFeatureCanonicalZeroCount (n + c) -
        criticalFeatureCanonicalZeroCount n) /
          criticalFeatureCanonicalZeroCount n) atTop (𝓝 0) := by
  have h := (tendsto_criticalFeatureCanonicalZeroCount_nat_add_div c).sub_const 1
  norm_num at h
  refine h.congr' ?_
  filter_upwards [eventually_criticalFeatureCanonicalZeroCount_pos] with n hN
  have hN0 : criticalFeatureCanonicalZeroCount n ≠ 0 := ne_of_gt hN
  field_simp

theorem tendsto_xiPosCriticalZeroCount_nat_add_sub_div_zero (c : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((xiPosCriticalZeroCount ((n + c : ℕ) : ℝ) -
          xiPosCriticalZeroCount (n : ℝ) : ℕ) : ℝ) /
            criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) := by
  have htotal := tendsto_criticalFeatureCanonicalZeroCount_nat_add_sub_div_zero c
  refine squeeze_zero'
    (eventually_criticalFeatureCanonicalZeroCount_pos.mono fun n hN => by positivity)
    ?_ htotal
  filter_upwards [eventually_criticalFeatureCanonicalZeroCount_pos] with n hN
  have hcrit := xiPosCriticalZeroCount_sub_le_xiPosZeroCount_sub
    (show (n : ℝ) ≤ ((n + c : ℕ) : ℝ) by exact_mod_cast Nat.le_add_right n c)
  have hbase := xiPosZeroCount_eq_xiZeroCount (T := (n : ℝ)) (by positivity)
  have hshift := xiPosZeroCount_eq_xiZeroCount (T := ((n + c : ℕ) : ℝ)) (by positivity)
  have htotalNat : xiPosZeroCount (n : ℝ) ≤
      xiPosZeroCount ((n + c : ℕ) : ℝ) := by
    unfold xiPosZeroCount
    exact Finset.sum_le_sum_of_subset (stripFinsetPos_subset_local
      (show (n : ℝ) ≤ ((n + c : ℕ) : ℝ) by exact_mod_cast Nat.le_add_right n c))
  have hbaseReal : (xiPosZeroCount (n : ℝ) : ℝ) =
      criticalFeatureCanonicalZeroCount n := by
    dsimp [criticalFeatureCanonicalZeroCount]
    exact_mod_cast hbase
  have hshiftReal : (xiPosZeroCount ((n + c : ℕ) : ℝ) : ℝ) =
      criticalFeatureCanonicalZeroCount (n + c) := by
    dsimp [criticalFeatureCanonicalZeroCount]
    exact_mod_cast hshift
  have hcritCast :
      ((xiPosCriticalZeroCount ((n + c : ℕ) : ℝ) -
          xiPosCriticalZeroCount (n : ℝ) : ℕ) : ℝ) ≤
        ((xiPosZeroCount ((n + c : ℕ) : ℝ) -
          xiPosZeroCount (n : ℝ) : ℕ) : ℝ) := by
    exact_mod_cast hcrit
  have hcritReal :
      ((xiPosCriticalZeroCount ((n + c : ℕ) : ℝ) -
          xiPosCriticalZeroCount (n : ℝ) : ℕ) : ℝ) ≤
        criticalFeatureCanonicalZeroCount (n + c) -
          criticalFeatureCanonicalZeroCount n := by
    rw [Nat.cast_sub htotalNat, hbaseReal, hshiftReal] at hcritCast
    exact hcritCast
  exact (div_le_div_iff_of_pos_right hN).2 hcritReal

theorem tendsto_criticalFeatureCanonicalZeroCount_nat_add_sub_div_shift_zero
    (c : ℕ) :
    Tendsto (fun n : ℕ =>
      (criticalFeatureCanonicalZeroCount (n + c) -
        criticalFeatureCanonicalZeroCount n) /
          criticalFeatureCanonicalZeroCount (n + c)) atTop (𝓝 0) := by
  have h :=
    (tendsto_criticalFeatureCanonicalZeroCount_nat_add_sub_div_zero c).div
      (tendsto_criticalFeatureCanonicalZeroCount_nat_add_div c)
      (by norm_num : (1 : ℝ) ≠ 0)
  have heq : ∀ᶠ n : ℕ in atTop,
      ((criticalFeatureCanonicalZeroCount (n + c) -
          criticalFeatureCanonicalZeroCount n) /
            criticalFeatureCanonicalZeroCount n) /
        (criticalFeatureCanonicalZeroCount (n + c) /
          criticalFeatureCanonicalZeroCount n) =
      (criticalFeatureCanonicalZeroCount (n + c) -
        criticalFeatureCanonicalZeroCount n) /
          criticalFeatureCanonicalZeroCount (n + c) := by
    filter_upwards [eventually_criticalFeatureCanonicalZeroCount_pos] with n hN
    have hN0 : criticalFeatureCanonicalZeroCount n ≠ 0 := ne_of_gt hN
    field_simp
  simpa only [zero_div] using h.congr' heq

theorem tendsto_xiPosCriticalZeroCount_nat_add_sub_div_shift_zero (c : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((xiPosCriticalZeroCount ((n + c : ℕ) : ℝ) -
          xiPosCriticalZeroCount (n : ℝ) : ℕ) : ℝ) /
            criticalFeatureCanonicalZeroCount (n + c))
      atTop (𝓝 0) := by
  have htotal :=
    tendsto_criticalFeatureCanonicalZeroCount_nat_add_sub_div_shift_zero c
  have hshiftPos : ∀ᶠ n : ℕ in atTop,
      0 < criticalFeatureCanonicalZeroCount (n + c) := by
    filter_upwards [eventually_criticalFeatureCanonicalZeroCount_pos] with n hNbase
    have hmono := xiZeroCount_mono
      (show (n : ℝ) ≤ ((n + c : ℕ) : ℝ) by exact_mod_cast Nat.le_add_right n c)
    have hmonoReal : (xiZeroCount (n : ℝ) : ℝ) ≤
        (xiZeroCount ((n + c : ℕ) : ℝ) : ℝ) := by
      exact_mod_cast hmono
    change 0 < (xiZeroCount (n : ℝ) : ℝ) at hNbase
    change 0 < (xiZeroCount ((n + c : ℕ) : ℝ) : ℝ)
    exact hNbase.trans_le hmonoReal
  refine squeeze_zero'
    (hshiftPos.mono fun n hN => by positivity)
    ?_ htotal
  filter_upwards [eventually_criticalFeatureCanonicalZeroCount_pos]
      with n hNbase
  have hNshift : 0 < criticalFeatureCanonicalZeroCount (n + c) := by
    have hmono := xiZeroCount_mono
      (show (n : ℝ) ≤ ((n + c : ℕ) : ℝ) by exact_mod_cast Nat.le_add_right n c)
    have hmonoReal : (xiZeroCount (n : ℝ) : ℝ) ≤
        (xiZeroCount ((n + c : ℕ) : ℝ) : ℝ) := by
      exact_mod_cast hmono
    change 0 < (xiZeroCount (n : ℝ) : ℝ) at hNbase
    change 0 < (xiZeroCount ((n + c : ℕ) : ℝ) : ℝ)
    exact hNbase.trans_le hmonoReal
  have hcrit := xiPosCriticalZeroCount_sub_le_xiPosZeroCount_sub
    (show (n : ℝ) ≤ ((n + c : ℕ) : ℝ) by exact_mod_cast Nat.le_add_right n c)
  have hbase := xiPosZeroCount_eq_xiZeroCount (T := (n : ℝ)) (by positivity)
  have hshift := xiPosZeroCount_eq_xiZeroCount (T := ((n + c : ℕ) : ℝ)) (by positivity)
  have htotalNat : xiPosZeroCount (n : ℝ) ≤
      xiPosZeroCount ((n + c : ℕ) : ℝ) := by
    unfold xiPosZeroCount
    exact Finset.sum_le_sum_of_subset (stripFinsetPos_subset_local
      (show (n : ℝ) ≤ ((n + c : ℕ) : ℝ) by exact_mod_cast Nat.le_add_right n c))
  have hbaseReal : (xiPosZeroCount (n : ℝ) : ℝ) =
      criticalFeatureCanonicalZeroCount n := by
    dsimp [criticalFeatureCanonicalZeroCount]
    exact_mod_cast hbase
  have hshiftReal : (xiPosZeroCount ((n + c : ℕ) : ℝ) : ℝ) =
      criticalFeatureCanonicalZeroCount (n + c) := by
    dsimp [criticalFeatureCanonicalZeroCount]
    exact_mod_cast hshift
  have hcritCast :
      ((xiPosCriticalZeroCount ((n + c : ℕ) : ℝ) -
          xiPosCriticalZeroCount (n : ℝ) : ℕ) : ℝ) ≤
        ((xiPosZeroCount ((n + c : ℕ) : ℝ) -
          xiPosZeroCount (n : ℝ) : ℕ) : ℝ) := by
    exact_mod_cast hcrit
  have hcritReal :
      ((xiPosCriticalZeroCount ((n + c : ℕ) : ℝ) -
          xiPosCriticalZeroCount (n : ℝ) : ℕ) : ℝ) ≤
        criticalFeatureCanonicalZeroCount (n + c) -
          criticalFeatureCanonicalZeroCount n := by
    rw [Nat.cast_sub htotalNat, hbaseReal, hshiftReal] at hcritCast
    exact hcritCast
  exact (div_le_div_iff_of_pos_right hNshift).2 hcritReal

theorem tendsto_xiPosCriticalZeroCount_sub_nat_sub_div_zero (c : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((xiPosCriticalZeroCount (n : ℝ) -
          xiPosCriticalZeroCount ((n - c : ℕ) : ℝ) : ℕ) : ℝ) /
            criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) := by
  rw [← Filter.tendsto_add_atTop_iff_nat c]
  simpa only [Nat.add_sub_cancel_right] using
    tendsto_xiPosCriticalZeroCount_nat_add_sub_div_shift_zero c

theorem tendsto_sourceBoundary_sub_four_pi_mul_xiPosCritical_div_zeroCount :
    Tendsto
      (fun n : ℕ =>
        (criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n -
          4 * Real.pi * (xiPosCriticalZeroCount (n : ℝ) : ℝ)) /
            criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let e : ℝ := ε / (8 * (Real.pi + 1))
  have he : 0 < e := by dsimp [e]; positivity
  have hmassNat : Tendsto
      (fun M : ℕ => ∫ y : ℝ in (-(M : ℝ))..(M : ℝ),
        criticalFeatureRealBoundaryWeight 0 y)
      atTop (𝓝 (2 * Real.pi)) := by
    simpa [Function.comp_def] using
      tendsto_intervalIntegral_criticalFeatureRealBoundaryWeight_atTop.comp
        tendsto_natCast_atTop_atTop
  rw [Metric.tendsto_atTop] at hmassNat
  obtain ⟨M, hM⟩ := hmassNat e he
  have hmass := hM M le_rfl
  rw [Real.dist_eq] at hmass
  have hplus := tendsto_xiPosCriticalZeroCount_nat_add_sub_div_zero 4
  rw [Metric.tendsto_atTop] at hplus
  obtain ⟨Nplus, hNplus⟩ := hplus e he
  have hminus := tendsto_xiPosCriticalZeroCount_sub_nat_sub_div_zero M
  rw [Metric.tendsto_atTop] at hminus
  obtain ⟨Nminus, hNminus⟩ := hminus e he
  obtain ⟨Npos, hNpos⟩ :=
    (Filter.eventually_atTop.1 eventually_criticalFeatureCanonicalZeroCount_pos)
  refine ⟨max M (max Nplus (max Nminus Npos)), fun n hn => ?_⟩
  have hnM : M ≤ n := by omega
  have hnPlus : Nplus ≤ n := by omega
  have hnMinus : Nminus ≤ n := by omega
  have hnPos : Npos ≤ n := by omega
  have hN : 0 < criticalFeatureCanonicalZeroCount n := hNpos n hnPos
  have hN0 : criticalFeatureCanonicalZeroCount n ≠ 0 := ne_of_gt hN
  have hplusNear := hNplus n hnPlus
  rw [Real.dist_eq, sub_zero, abs_lt] at hplusNear
  have hplusBound :
      ((xiPosCriticalZeroCount ((n + 4 : ℕ) : ℝ) -
          xiPosCriticalZeroCount (n : ℝ) : ℕ) : ℝ) /
          criticalFeatureCanonicalZeroCount n < e := hplusNear.2
  have hminusNear := hNminus n hnMinus
  rw [Real.dist_eq, sub_zero, abs_lt] at hminusNear
  have hminusBound :
      ((xiPosCriticalZeroCount (n : ℝ) -
          xiPosCriticalZeroCount ((n - M : ℕ) : ℝ) : ℕ) : ℝ) /
          criticalFeatureCanonicalZeroCount n < e := hminusNear.2
  have hcritPlusMono : xiPosCriticalZeroCount (n : ℝ) ≤
      xiPosCriticalZeroCount ((n + 4 : ℕ) : ℝ) :=
    monotone_xiPosCriticalZeroCount_local
      (show (n : ℝ) ≤ ((n + 4 : ℕ) : ℝ) by norm_num)
  have hcritMinusMono : xiPosCriticalZeroCount ((n - M : ℕ) : ℝ) ≤
      xiPosCriticalZeroCount (n : ℝ) :=
    monotone_xiPosCriticalZeroCount_local
      (show ((n - M : ℕ) : ℝ) ≤ (n : ℝ) by exact_mod_cast Nat.sub_le n M)
  have hplusCast :
      ((xiPosCriticalZeroCount ((n + 4 : ℕ) : ℝ) -
          xiPosCriticalZeroCount (n : ℝ) : ℕ) : ℝ) =
        (xiPosCriticalZeroCount ((n + 4 : ℕ) : ℝ) : ℝ) -
          (xiPosCriticalZeroCount (n : ℝ) : ℝ) := by
    rw [Nat.cast_sub hcritPlusMono]
  have hminusCast :
      ((xiPosCriticalZeroCount (n : ℝ) -
          xiPosCriticalZeroCount ((n - M : ℕ) : ℝ) : ℕ) : ℝ) =
        (xiPosCriticalZeroCount (n : ℝ) : ℝ) -
          (xiPosCriticalZeroCount ((n - M : ℕ) : ℝ) : ℝ) := by
    rw [Nat.cast_sub hcritMinusMono]
  have hupperB :
      criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n ≤
        4 * Real.pi *
          (xiPosCriticalZeroCount ((n + 4 : ℕ) : ℝ) : ℝ) := by
    simpa using
      criticalFeatureSourceBoundaryPhaseAverage_le_xiPosCriticalZeroCount_add_four n
  have hupperD :
      (criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n -
          4 * Real.pi * (xiPosCriticalZeroCount (n : ℝ) : ℝ)) /
          criticalFeatureCanonicalZeroCount n ≤
        (4 * Real.pi *
          ((xiPosCriticalZeroCount ((n + 4 : ℕ) : ℝ) : ℝ) -
            (xiPosCriticalZeroCount (n : ℝ) : ℝ))) /
          criticalFeatureCanonicalZeroCount n := by
    apply (div_le_div_iff_of_pos_right hN).2
    nlinarith
  have hupperSmall :
      (4 * Real.pi *
          ((xiPosCriticalZeroCount ((n + 4 : ℕ) : ℝ) : ℝ) -
            (xiPosCriticalZeroCount (n : ℝ) : ℝ))) /
          criticalFeatureCanonicalZeroCount n < 4 * Real.pi * e := by
    rw [← hplusCast, mul_div_assoc]
    exact mul_lt_mul_of_pos_left hplusBound (by positivity)
  have hupperEps :
      (criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n -
          4 * Real.pi * (xiPosCriticalZeroCount (n : ℝ) : ℝ)) /
          criticalFeatureCanonicalZeroCount n < ε := by
    have hconst : 4 * Real.pi * e < ε := by
      have hden : 0 < 8 * (Real.pi + 1) := by positivity
      have haux :
          (4 * Real.pi * ε) / (8 * (Real.pi + 1)) < ε := by
        apply (div_lt_iff₀ hden).2
        nlinarith [Real.pi_pos]
      dsimp [e]
      convert haux using 1
      ring
    exact hupperD.trans_lt (hupperSmall.trans hconst)
  have hTA : ((n - M : ℕ) : ℝ) + (M : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast (show n - M + M ≤ n + 1 by omega)
  have hlowerB := criticalFeatureSourceBoundaryPhaseAverage_lower_xiPosCriticalZeroCount
    n ((n - M : ℕ) : ℝ) (M : ℝ) (by positivity) hTA
  have hmassDeficit :
      4 * Real.pi -
          2 * (∫ y : ℝ in (-(M : ℝ))..(M : ℝ),
            criticalFeatureRealBoundaryWeight 0 y) < 2 * e := by
    rw [abs_lt] at hmass
    nlinarith
  have hCprevNonneg :
      (0 : ℝ) ≤ xiPosCriticalZeroCount ((n - M : ℕ) : ℝ) := by positivity
  have hCprevLeN :
      (xiPosCriticalZeroCount ((n - M : ℕ) : ℝ) : ℝ) ≤
        criticalFeatureCanonicalZeroCount n := by
    have hprevTotal := xiPosCriticalZeroCount_cast_le_canonicalZeroCount (n - M)
    have hmono := xiZeroCount_mono
      (show ((n - M : ℕ) : ℝ) ≤ (n : ℝ) by exact_mod_cast Nat.sub_le n M)
    have hmonoReal : criticalFeatureCanonicalZeroCount (n - M) ≤
        criticalFeatureCanonicalZeroCount n := by
      dsimp [criticalFeatureCanonicalZeroCount]
      exact_mod_cast hmono
    exact hprevTotal.trans hmonoReal
  have hcoefMul :
      (4 * Real.pi -
          2 * (∫ y : ℝ in (-(M : ℝ))..(M : ℝ),
            criticalFeatureRealBoundaryWeight 0 y)) *
          (xiPosCriticalZeroCount ((n - M : ℕ) : ℝ) : ℝ) ≤
        2 * e * (xiPosCriticalZeroCount ((n - M : ℕ) : ℝ) : ℝ) :=
    mul_le_mul_of_nonneg_right hmassDeficit.le hCprevNonneg
  have hsmallCount :
      2 * e * (xiPosCriticalZeroCount ((n - M : ℕ) : ℝ) : ℝ) ≤
        2 * e * criticalFeatureCanonicalZeroCount n :=
    mul_le_mul_of_nonneg_left hCprevLeN (by positivity)
  have hnumLower :
      4 * Real.pi * (xiPosCriticalZeroCount (n : ℝ) : ℝ) -
          criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n ≤
        4 * Real.pi *
            ((xiPosCriticalZeroCount (n : ℝ) : ℝ) -
              (xiPosCriticalZeroCount ((n - M : ℕ) : ℝ) : ℝ)) +
          2 * e * criticalFeatureCanonicalZeroCount n := by
    nlinarith [hcoefMul.trans hsmallCount]
  have hlowerSmall :
      (4 * Real.pi * (xiPosCriticalZeroCount (n : ℝ) : ℝ) -
          criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n) /
          criticalFeatureCanonicalZeroCount n < 4 * Real.pi * e + 2 * e := by
    have hdiv := (div_le_div_iff_of_pos_right hN).2 hnumLower
    calc
      (4 * Real.pi * (xiPosCriticalZeroCount (n : ℝ) : ℝ) -
          criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n) /
          criticalFeatureCanonicalZeroCount n ≤
        (4 * Real.pi *
            ((xiPosCriticalZeroCount (n : ℝ) : ℝ) -
              (xiPosCriticalZeroCount ((n - M : ℕ) : ℝ) : ℝ)) +
          2 * e * criticalFeatureCanonicalZeroCount n) /
            criticalFeatureCanonicalZeroCount n := hdiv
      _ = 4 * Real.pi *
            (((xiPosCriticalZeroCount (n : ℝ) : ℝ) -
              (xiPosCriticalZeroCount ((n - M : ℕ) : ℝ) : ℝ)) /
            criticalFeatureCanonicalZeroCount n) + 2 * e := by
          field_simp
      _ < 4 * Real.pi * e + 2 * e := by
          rw [hminusCast] at hminusBound
          have hmul :=
            mul_lt_mul_of_pos_left hminusBound
              (show 0 < 4 * Real.pi by positivity)
          linarith
  have hlowerEps :
      -ε <
        (criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n -
          4 * Real.pi * (xiPosCriticalZeroCount (n : ℝ) : ℝ)) /
            criticalFeatureCanonicalZeroCount n := by
    have hconst : 4 * Real.pi * e + 2 * e < ε := by
      dsimp [e]
      have hden : 0 < 8 * (Real.pi + 1) := by positivity
      field_simp
      nlinarith [Real.pi_pos]
    have hsmall := hlowerSmall.trans hconst
    have hnegEq :
        -((criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n -
          4 * Real.pi * (xiPosCriticalZeroCount (n : ℝ) : ℝ)) /
            criticalFeatureCanonicalZeroCount n) =
          (4 * Real.pi * (xiPosCriticalZeroCount (n : ℝ) : ℝ) -
            criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n) /
              criticalFeatureCanonicalZeroCount n := by ring
    rw [← hnegEq] at hsmall
    linarith
  rw [Real.dist_eq, sub_zero, abs_lt]
  exact ⟨hlowerEps, hupperEps⟩

/-- The source boundary is asymptotically exactly `4π` times the canonical critical-line
multiplicity. -/
theorem tendsto_sourceBoundary_sub_four_pi_mul_criticalLineCount_div_zeroCount :
    Tendsto
      (fun n : ℕ =>
        (criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n -
          4 * Real.pi * criticalFeatureCanonicalCriticalLineCount n) /
            criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) := by
  simpa only [criticalFeatureCanonicalCriticalLineCount_eq_xiPosCriticalZeroCount] using
    tendsto_sourceBoundary_sub_four_pi_mul_xiPosCritical_div_zeroCount

/-- Exact asymptotic detector: HCF phase covariance is precisely `4π` times off-line
multiplicity, normalized by the total zero count. -/
theorem tendsto_criticalFeaturePhaseCovariance_sub_four_pi_mul_offLineMass_div_zeroCount :
    Tendsto
      (fun n : ℕ =>
        (criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n -
          4 * Real.pi *
            (criticalFeatureCanonicalZeroCount n -
              criticalFeatureCanonicalCriticalLineCount n)) /
            criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) := by
  have htotal :=
    tendsto_criticalFeaturePhaseCovariance_add_boundary_div_zeroCount.sub_const
      (4 * Real.pi)
  have h := htotal.sub
    tendsto_sourceBoundary_sub_four_pi_mul_criticalLineCount_div_zeroCount
  have hzero : Tendsto
      (fun n : ℕ =>
        ((criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n +
            criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n) /
              criticalFeatureCanonicalZeroCount n - 4 * Real.pi) -
          (criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n -
            4 * Real.pi * criticalFeatureCanonicalCriticalLineCount n) /
              criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) := by
    simpa using h
  refine hzero.congr' ?_
  filter_upwards [eventually_criticalFeatureCanonicalZeroCount_pos] with n hN
  have hN0 : criticalFeatureCanonicalZeroCount n ≠ 0 := ne_of_gt hN
  field_simp
  ring

/-- Sharp `75%` source gate.  The phase-averaged, zero-index-free HCF covariance has ceiling `π`
if and only if the canonical critical-line multiplicity has asymptotic lower proportion `3/4`.
Thus the old `4/25` covariance target was sufficient but drastically stronger than necessary. -/
theorem criticalFeaturePhaseCovariance_pi_upper_iff_threeQuarters_criticalLine :
    CriticalFeatureCanonicalAsymptoticUpper
        criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage Real.pi ↔
      CriticalFeatureCanonicalAsymptoticLower
        criticalFeatureCanonicalCriticalLineCount (3 / 4) := by
  let D : ℕ → ℝ := fun n =>
    4 * Real.pi *
      (criticalFeatureCanonicalZeroCount n -
        criticalFeatureCanonicalCriticalLineCount n)
  have htransfer :
      CriticalFeatureCanonicalAsymptoticUpper
          criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage Real.pi ↔
        CriticalFeatureCanonicalAsymptoticUpper D Real.pi :=
    criticalFeatureCanonicalAsymptoticUpper_iff_of_sub_div_tendsto_zero
      tendsto_criticalFeaturePhaseCovariance_sub_four_pi_mul_offLineMass_div_zeroCount
  rw [htransfer]
  constructor
  · intro hupper ε hε
    have hD := hupper (4 * Real.pi * ε) (by positivity)
    filter_upwards [hD, eventually_criticalFeatureCanonicalZeroCount_pos] with n hDn hN
    dsimp [D] at hDn
    nlinarith [Real.pi_pos]
  · intro hlower ε hε
    have hline := hlower (ε / (4 * Real.pi)) (by positivity)
    filter_upwards [hline, eventually_criticalFeatureCanonicalZeroCount_pos]
      with n hlineN hN
    dsimp [D]
    have hscaled := mul_le_mul_of_nonneg_left hlineN
      (show 0 ≤ 4 * Real.pi by positivity)
    have hcoef :
        4 * Real.pi * (3 / 4 - ε / (4 * Real.pi)) =
          3 * Real.pi - ε := by
      field_simp
    rw [← mul_assoc, hcoef] at hscaled
    nlinarith [Real.pi_pos]

end

end RHTower
