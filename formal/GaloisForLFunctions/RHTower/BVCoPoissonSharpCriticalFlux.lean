import GaloisForLFunctions.RHTower.BVCoPoissonSharpCriticalFluxCore
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Filter Topology

namespace RHTower

noncomputable section

def sharpCriticalFlux (T : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..T, t * sharpCoPoissonP t ^ 2

lemma intervalIntegrable_sharpCriticalFlux {T : ℝ} (hT : 2 ≤ T) :
    IntervalIntegrable (fun t : ℝ => t * sharpCoPoissonP t ^ 2) MeasureTheory.volume 2 T := by
  obtain ⟨M, hM⟩ := exists_nat_gt (T / 2)
  apply (intervalIntegrable_sharpCriticalFlux_cutoff M).mono_set
  have hcut : (2 : ℝ) ≤ 2 * (M + 1) := by
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  rw [Set.uIcc_of_le hT, Set.uIcc_of_le hcut]
  apply Set.Icc_subset_Icc le_rfl
  have : T < 2 * (M : ℝ) := by linarith
  linarith

lemma sharpCriticalFlux_mono {A B : ℝ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    sharpCriticalFlux A ≤ sharpCriticalFlux B := by
  unfold sharpCriticalFlux
  apply intervalIntegral.integral_mono_interval le_rfl hA hAB
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (by linarith [ht.1]) (sq_nonneg _)
  · exact intervalIntegrable_sharpCriticalFlux (hA.trans hAB)

lemma sharpCriticalFlux_cutoff_eq (M : ℕ) :
    sharpCriticalFlux (2 * ((M : ℝ) + 1)) = sharpCriticalPartialEnergy M := by
  unfold sharpCriticalFlux
  simpa only [Nat.cast_add, Nat.cast_one] using integral_sharpCriticalFlux_cutoff_eq M

lemma tendsto_floor_half_atTop :
    Tendsto (fun T : ℝ => ⌊T / 2⌋₊) atTop atTop := by
  have hhalf : Tendsto (fun T : ℝ => T / 2) atTop atTop := by
    simpa only [id_eq, div_eq_mul_inv] using
      (tendsto_id.atTop_mul_const (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹))
  exact tendsto_nat_floor_atTop.comp hhalf

lemma tendsto_floor_half_sub_one_atTop :
    Tendsto (fun T : ℝ => ⌊T / 2⌋₊ - 1) atTop atTop := by
  rw [tendsto_atTop]
  intro N
  filter_upwards [(tendsto_floor_half_atTop.eventually (eventually_ge_atTop (N + 1)))] with T hT
  omega

lemma floor_half_cutoff_bounds {T : ℝ} (hT : 4 ≤ T) :
    2 * (⌊T / 2⌋₊ : ℝ) ≤ T ∧ T < 2 * ((⌊T / 2⌋₊ : ℝ) + 1) := by
  have hnonneg : 0 ≤ T / 2 := by positivity
  constructor
  · have h := Nat.floor_le hnonneg
    linarith
  · have h := Nat.lt_floor_add_one (T / 2)
    linarith

lemma floor_half_pos {T : ℝ} (hT : 4 ≤ T) : 0 < ⌊T / 2⌋₊ := by
  rw [Nat.floor_pos]
  linarith

lemma sharpCriticalFlux_floor_sandwich {T : ℝ} (hT : 4 ≤ T) :
    sharpCriticalPartialEnergy (⌊T / 2⌋₊ - 1) ≤ sharpCriticalFlux T ∧
      sharpCriticalFlux T ≤ sharpCriticalPartialEnergy ⌊T / 2⌋₊ := by
  have hm := floor_half_pos hT
  have hb := floor_half_cutoff_bounds hT
  constructor
  · rw [← sharpCriticalFlux_cutoff_eq (⌊T / 2⌋₊ - 1)]
    have hend : 2 * (((⌊T / 2⌋₊ - 1 : ℕ) : ℝ) + 1) =
        2 * (⌊T / 2⌋₊ : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hend]
    exact sharpCriticalFlux_mono (by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
      rw [hk]
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      push_cast
      linarith) hb.1
  · rw [← sharpCriticalFlux_cutoff_eq ⌊T / 2⌋₊]
    exact sharpCriticalFlux_mono (by linarith) hb.2.le

def sharpCutoffLog (M : ℕ) : ℝ :=
  Real.log (2 * ((M : ℝ) + 1))

lemma sharpCutoffLog_pos (M : ℕ) : 0 < sharpCutoffLog M := by
  unfold sharpCutoffLog
  apply Real.log_pos
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  linarith

lemma tendsto_sharpCutoffLog_atTop :
    Tendsto sharpCutoffLog atTop atTop := by
  change Tendsto (fun M : ℕ => Real.log (2 * ((M : ℝ) + 1))) atTop atTop
  exact tendsto_log_sharpCutoff_atTop

lemma tendsto_sharpCutoffLog_succ_sub :
    Tendsto (fun M : ℕ => sharpCutoffLog (M + 1) - sharpCutoffLog M)
      atTop (nhds 0) := by
  have h := Real.tendsto_log_nat_add_one_sub_log.comp (Filter.tendsto_add_atTop_nat 1)
  convert h using 1
  funext M
  unfold sharpCutoffLog
  rw [Real.log_mul (by norm_num) (by positivity),
    Real.log_mul (by norm_num) (by positivity)]
  push_cast
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  ring_nf

lemma tendsto_sharpCutoffLog_div_succ :
    Tendsto (fun M : ℕ => sharpCutoffLog M / sharpCutoffLog (M + 1))
      atTop (nhds 1) := by
  have hnext : Tendsto (fun M : ℕ => sharpCutoffLog (M + 1)) atTop atTop :=
    tendsto_sharpCutoffLog_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hvanish := tendsto_sharpCutoffLog_succ_sub.div_atTop hnext
  have hlimit : Tendsto (fun M : ℕ =>
      1 - (sharpCutoffLog (M + 1) - sharpCutoffLog M) / sharpCutoffLog (M + 1))
      atTop (nhds 1) := by simpa using (tendsto_const_nhds.sub hvanish)
  apply hlimit.congr'
  filter_upwards with M
  have hne := (sharpCutoffLog_pos (M + 1)).ne'
  field_simp
  ring

lemma tendsto_sharpCutoffLog_succ_div :
    Tendsto (fun M : ℕ => sharpCutoffLog (M + 1) / sharpCutoffLog M)
      atTop (nhds 1) := by
  have hvanish := tendsto_sharpCutoffLog_succ_sub.div_atTop
    tendsto_sharpCutoffLog_atTop
  have hlimit : Tendsto (fun M : ℕ =>
      1 + (sharpCutoffLog (M + 1) - sharpCutoffLog M) / sharpCutoffLog M)
      atTop (nhds 1) := by simpa using (tendsto_const_nhds.add hvanish)
  apply hlimit.congr'
  filter_upwards with M
  have hne := (sharpCutoffLog_pos M).ne'
  field_simp
  ring

lemma tendsto_nat_sub_one_atTop :
    Tendsto (fun M : ℕ => M - 1) atTop atTop := by
  rw [tendsto_atTop]
  intro N
  filter_upwards [eventually_ge_atTop (N + 1)] with M hM
  omega

lemma tendsto_lower_sharpCriticalFlux_ratio :
    Tendsto (fun M : ℕ =>
      sharpCriticalPartialEnergy (M - 1) / sharpCutoffLog M) atTop
      (nhds (1 / 4)) := by
  have hbase : Tendsto (fun M : ℕ =>
      sharpCriticalPartialEnergy (M - 1) / sharpCutoffLog (M - 1)) atTop
      (nhds (1 / 4)) := by
    have h := tendsto_sharpCriticalPartialEnergy_div_log_cutoff.comp
      tendsto_nat_sub_one_atTop
    change Tendsto (fun M : ℕ => sharpCriticalPartialEnergy (M - 1) /
      Real.log (2 * (((M - 1 : ℕ) : ℝ) + 1))) atTop (nhds (1 / 4)) at h
    simpa only [sharpCutoffLog] using h
  have hratio := tendsto_sharpCutoffLog_div_succ.comp tendsto_nat_sub_one_atTop
  have hprod : Tendsto (fun M : ℕ =>
      (sharpCriticalPartialEnergy (M - 1) / sharpCutoffLog (M - 1)) *
        (sharpCutoffLog (M - 1) / sharpCutoffLog ((M - 1) + 1))) atTop
      (nhds (1 / 4)) := by
    have h := hbase.mul hratio
    change Tendsto (fun M : ℕ =>
      (sharpCriticalPartialEnergy (M - 1) / sharpCutoffLog (M - 1)) *
        (sharpCutoffLog (M - 1) / sharpCutoffLog ((M - 1) + 1))) atTop
      (nhds ((1 / 4) * 1)) at h
    simpa only [mul_one] using h
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hs : M - 1 + 1 = M := by omega
  rw [hs]
  have hne := (sharpCutoffLog_pos (M - 1)).ne'
  field_simp

lemma tendsto_upper_sharpCriticalFlux_ratio :
    Tendsto (fun M : ℕ =>
      sharpCriticalPartialEnergy M / sharpCutoffLog (M - 1)) atTop
      (nhds (1 / 4)) := by
  have hbase : Tendsto (fun M : ℕ =>
      sharpCriticalPartialEnergy M / sharpCutoffLog M) atTop (nhds (1 / 4)) := by
    simpa only [sharpCutoffLog] using
      tendsto_sharpCriticalPartialEnergy_div_log_cutoff
  have hratio := tendsto_sharpCutoffLog_succ_div.comp tendsto_nat_sub_one_atTop
  have hprod : Tendsto (fun M : ℕ =>
      (sharpCriticalPartialEnergy M / sharpCutoffLog M) *
        (sharpCutoffLog ((M - 1) + 1) / sharpCutoffLog (M - 1))) atTop
      (nhds (1 / 4)) := by
    have h := hbase.mul hratio
    change Tendsto (fun M : ℕ =>
      (sharpCriticalPartialEnergy M / sharpCutoffLog M) *
        (sharpCutoffLog ((M - 1) + 1) / sharpCutoffLog (M - 1))) atTop
      (nhds ((1 / 4) * 1)) at h
    simpa only [mul_one] using h
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hs : M - 1 + 1 = M := by omega
  rw [hs]
  have hne := (sharpCutoffLog_pos M).ne'
  field_simp

lemma sharpCriticalPartialEnergy_nonneg (M : ℕ) :
    0 ≤ sharpCriticalPartialEnergy M := by
  unfold sharpCriticalPartialEnergy
  apply Finset.sum_nonneg
  intro n hn
  unfold sharpCriticalEnergy
  positivity

/-- Exact continuous logarithmic boundary flux law, with no subsequence restriction. -/
theorem tendsto_sharpCriticalFlux_div_log :
    Tendsto (fun T : ℝ => sharpCriticalFlux T / Real.log T) atTop
      (nhds (1 / 4)) := by
  have hlower := tendsto_lower_sharpCriticalFlux_ratio.comp tendsto_floor_half_atTop
  have hupper := tendsto_upper_sharpCriticalFlux_ratio.comp tendsto_floor_half_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_ge_atTop 4] with T hT
    let m := ⌊T / 2⌋₊
    have hsand := sharpCriticalFlux_floor_sandwich hT
    have hb := floor_half_cutoff_bounds hT
    have hm : 0 < m := floor_half_pos hT
    have hTlog : 0 < Real.log T := Real.log_pos (by linarith)
    have hUpperLog : Real.log T ≤ sharpCutoffLog m := by
      unfold sharpCutoffLog
      refine Real.strictMonoOn_log.monotoneOn ?_ ?_ hb.2.le
      · exact Set.mem_Ioi.2 (by linarith)
      · exact Set.mem_Ioi.2 (by
          have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          linarith)
    calc
      sharpCriticalPartialEnergy (m - 1) / sharpCutoffLog m ≤
          sharpCriticalPartialEnergy (m - 1) / Real.log T :=
        div_le_div_of_nonneg_left (sharpCriticalPartialEnergy_nonneg _) hTlog hUpperLog
      _ ≤ sharpCriticalFlux T / Real.log T :=
        div_le_div_of_nonneg_right hsand.1 hTlog.le
  · filter_upwards [eventually_ge_atTop 4] with T hT
    let m := ⌊T / 2⌋₊
    have hsand := sharpCriticalFlux_floor_sandwich hT
    have hb := floor_half_cutoff_bounds hT
    have hm : 0 < m := floor_half_pos hT
    have hTlog : 0 < Real.log T := Real.log_pos (by linarith)
    have hsub : m - 1 + 1 = m := by omega
    have hLowerArg : 2 * (((m - 1 : ℕ) : ℝ) + 1) = 2 * (m : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have hLowerLog : sharpCutoffLog (m - 1) ≤ Real.log T := by
      unfold sharpCutoffLog
      rw [hLowerArg]
      refine Real.strictMonoOn_log.monotoneOn ?_ ?_ hb.1
      · exact Set.mem_Ioi.2 (by
          have hmR : (0 : ℝ) < m := by
            obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
            rw [hk]
            push_cast
            positivity
          positivity)
      · exact Set.mem_Ioi.2 (by linarith)
    have hLowerLogPos : 0 < sharpCutoffLog (m - 1) := sharpCutoffLog_pos _
    have hflux : 0 ≤ sharpCriticalFlux T :=
      (sharpCriticalPartialEnergy_nonneg _).trans hsand.1
    calc
      sharpCriticalFlux T / Real.log T ≤
          sharpCriticalFlux T / sharpCutoffLog (m - 1) :=
        div_le_div_of_nonneg_left hflux hLowerLogPos hLowerLog
      _ ≤ sharpCriticalPartialEnergy m / sharpCutoffLog (m - 1) :=
        div_le_div_of_nonneg_right hsand.2 hLowerLogPos.le

lemma sharpCoPoissonP_zero_one {t : ℝ} (_ht0 : 0 < t) (ht1 : t < 1) :
    sharpCoPoissonP t = -Real.log 2 := by
  simp [sharpCoPoissonP, ht1]

lemma sharpCoPoissonP_one_two {t : ℝ} (ht0 : 1 < t) (ht1 : t < 2) :
    sharpCoPoissonP t = 1 - Real.log 2 := by
  simp [sharpCoPoissonP, ht1, not_lt_of_ge ht0.le]

lemma intervalIntegrable_zero_one_criticalFlux :
    IntervalIntegrable (fun t : ℝ => t * sharpCoPoissonP t ^ 2) MeasureTheory.volume 0 1 := by
  have hcont : Continuous (fun t : ℝ => t * (-Real.log 2) ^ 2) :=
    continuous_id.mul continuous_const
  apply (hcont.intervalIntegrable _ _).congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc,
    (MeasureTheory.volume.ae_ne (1 : ℝ)).filter_mono MeasureTheory.ae_restrict_le]
      with t hmem ht
  rw [Set.uIoc_of_le (by norm_num), Set.mem_Ioc] at hmem
  rw [sharpCoPoissonP_zero_one hmem.1 (lt_of_le_of_ne hmem.2 ht)]

lemma intervalIntegrable_one_two_criticalFlux :
    IntervalIntegrable (fun t : ℝ => t * sharpCoPoissonP t ^ 2) MeasureTheory.volume 1 2 := by
  have hcont : Continuous (fun t : ℝ => t * (1 - Real.log 2) ^ 2) :=
    continuous_id.mul continuous_const
  apply (hcont.intervalIntegrable _ _).congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc,
    (MeasureTheory.volume.ae_ne (2 : ℝ)).filter_mono MeasureTheory.ae_restrict_le]
      with t hmem ht
  rw [Set.uIoc_of_le (by norm_num), Set.mem_Ioc] at hmem
  rw [sharpCoPoissonP_one_two hmem.1 (lt_of_le_of_ne hmem.2 ht)]

lemma intervalIntegrable_zero_two_criticalFlux :
    IntervalIntegrable (fun t : ℝ => t * sharpCoPoissonP t ^ 2) MeasureTheory.volume 0 2 :=
  intervalIntegrable_zero_one_criticalFlux.trans intervalIntegrable_one_two_criticalFlux

def sharpCriticalFluxFromZero (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, t * sharpCoPoissonP t ^ 2

lemma sharpCriticalFluxFromZero_eq_add {T : ℝ} (hT : 2 ≤ T) :
    sharpCriticalFluxFromZero T = sharpCriticalFluxFromZero 2 + sharpCriticalFlux T := by
  unfold sharpCriticalFluxFromZero sharpCriticalFlux
  exact (intervalIntegral.integral_add_adjacent_intervals
    intervalIntegrable_zero_two_criticalFlux (intervalIntegrable_sharpCriticalFlux hT)).symm

/-- The paper theorem `(1/4) log T`: exact source flux from zero, for arbitrary real cutoffs. -/
theorem tendsto_sharpCriticalFluxFromZero_div_log :
    Tendsto (fun T : ℝ => sharpCriticalFluxFromZero T / Real.log T) atTop
      (nhds (1 / 4)) := by
  have hconst : Tendsto (fun T : ℝ => sharpCriticalFluxFromZero 2 / Real.log T)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h := hconst.add tendsto_sharpCriticalFlux_div_log
  have h' : Tendsto (fun T : ℝ =>
      sharpCriticalFluxFromZero 2 / Real.log T + sharpCriticalFlux T / Real.log T)
      atTop (nhds (1 / 4)) := by
    convert h using 1
    ring
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 2] with T hT
  rw [sharpCriticalFluxFromZero_eq_add hT]
  ring

lemma sharpOddError_le_inv (m : ℕ) (hm : 0 < m) :
    sharpOddError m ≤ 1 / (m : ℝ) := by
  have hpos := sharpHarmonicError_pos m hm
  unfold sharpOddError
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrecip : 1 / (2 * m + 1 : ℝ) ≤ 1 / (m : ℝ) := by
    apply one_div_le_one_div_of_le hmR
    linarith
  linarith

lemma sharpCoPoissonP_abs_le_inv_floor {t : ℝ} (ht : 2 ≤ t) :
    |sharpCoPoissonP t| ≤ 1 / (⌊t / 2⌋₊ : ℝ) := by
  let m := ⌊t / 2⌋₊
  have hm : 0 < m := by
    unfold m
    rw [Nat.floor_pos]
    linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ht1 : ¬t < 1 := by linarith
  have ht2 : ¬t < 2 := by linarith
  unfold sharpCoPoissonP
  rw [if_neg ht1, if_neg ht2]
  change |if t < 2 * (m : ℝ) + 1 then -sharpHarmonicError m else sharpOddError m| ≤ _
  split_ifs with hcell
  · rw [abs_neg, abs_of_pos (sharpHarmonicError_pos m hm)]
    calc
      sharpHarmonicError m ≤ 1 / (4 * (m : ℝ)) := (sharpHarmonicError_bounds m hm).2
      _ ≤ 1 / (m : ℝ) := by
        apply one_div_le_one_div_of_le (by positivity)
        linarith
  · rw [abs_of_pos (sharpOddError_pos m hm)]
    exact sharpOddError_le_inv m hm

lemma sharpCoPoissonP_abs_le_four_div {t : ℝ} (ht : 2 ≤ t) :
    |sharpCoPoissonP t| ≤ 4 / t := by
  let m := ⌊t / 2⌋₊
  have hm : 0 < m := by
    unfold m
    rw [Nat.floor_pos]
    linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htpos : 0 < t := by linarith
  have hfloor := Nat.lt_floor_add_one (t / 2)
  have ht4m : t ≤ 4 * (m : ℝ) := by
    have hm1 : (1 : ℝ) ≤ m := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
      rw [hk]
      push_cast
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    change t / 2 < (m : ℝ) + 1 at hfloor
    linarith
  calc
    |sharpCoPoissonP t| ≤ 1 / (m : ℝ) := sharpCoPoissonP_abs_le_inv_floor ht
    _ ≤ 4 / t := (div_le_div_iff₀ hmR htpos).2 (by simpa using ht4m)

lemma sharpCoPoissonP_sq_le_rpow_majorant {t : ℝ} (ht : 2 < t) :
    sharpCoPoissonP t ^ 2 ≤ 16 * t ^ (-2 : ℝ) := by
  have htpos : 0 < t := by linarith
  have habs := sharpCoPoissonP_abs_le_four_div ht.le
  have hfour : 0 ≤ 4 / t := by positivity
  have hsq : |sharpCoPoissonP t| ^ 2 ≤ (4 / t) ^ 2 := by nlinarith [abs_nonneg (sharpCoPoissonP t)]
  calc
    sharpCoPoissonP t ^ 2 = |sharpCoPoissonP t| ^ 2 := by rw [sq_abs]
    _ ≤ (4 / t) ^ 2 := hsq
    _ = 16 * t ^ (-2 : ℝ) := by
      rw [show (-2 : ℝ) = -(2 : ℝ) by ring, Real.rpow_neg htpos.le]
      field_simp
      norm_num [mul_comm]

lemma integrableOn_sharpCoPoissonP_sq_Ioi_two :
    MeasureTheory.IntegrableOn (fun t : ℝ => sharpCoPoissonP t ^ 2) (Set.Ioi 2) := by
  have hmajor : MeasureTheory.IntegrableOn (fun t : ℝ => 16 * t ^ (-2 : ℝ))
      (Set.Ioi 2) :=
    (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := 2) (by norm_num) (by norm_num)).const_mul 16
  apply hmajor.mono'
  · exact (measurable_sharpCoPoissonP.pow_const 2).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sharpCoPoissonP_sq_le_rpow_majorant ht

lemma intervalIntegrable_zero_one_sharpCoPoissonP_sq :
    IntervalIntegrable (fun t : ℝ => sharpCoPoissonP t ^ 2) MeasureTheory.volume 0 1 := by
  have hcont : Continuous (fun _ : ℝ => (-Real.log 2) ^ 2) := continuous_const
  apply (hcont.intervalIntegrable _ _).congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc,
    (MeasureTheory.volume.ae_ne (1 : ℝ)).filter_mono MeasureTheory.ae_restrict_le]
      with t hmem ht
  rw [Set.uIoc_of_le (by norm_num), Set.mem_Ioc] at hmem
  rw [sharpCoPoissonP_zero_one hmem.1 (lt_of_le_of_ne hmem.2 ht)]

lemma intervalIntegrable_one_two_sharpCoPoissonP_sq :
    IntervalIntegrable (fun t : ℝ => sharpCoPoissonP t ^ 2) MeasureTheory.volume 1 2 := by
  have hcont : Continuous (fun _ : ℝ => (1 - Real.log 2) ^ 2) := continuous_const
  apply (hcont.intervalIntegrable _ _).congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc,
    (MeasureTheory.volume.ae_ne (2 : ℝ)).filter_mono MeasureTheory.ae_restrict_le]
      with t hmem ht
  rw [Set.uIoc_of_le (by norm_num), Set.mem_Ioc] at hmem
  rw [sharpCoPoissonP_one_two hmem.1 (lt_of_le_of_ne hmem.2 ht)]

/-- Ordinary Burnol carrier survives: the sharp source is square-integrable. -/
theorem integrableOn_sharpCoPoissonP_sq_Ioi_zero :
    MeasureTheory.IntegrableOn (fun t : ℝ => sharpCoPoissonP t ^ 2) (Set.Ioi 0) := by
  have hinit : MeasureTheory.IntegrableOn (fun t : ℝ => sharpCoPoissonP t ^ 2)
      (Set.Ioc 0 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (intervalIntegrable_zero_one_sharpCoPoissonP_sq.trans
        intervalIntegrable_one_two_sharpCoPoissonP_sq)
  have h := hinit.union integrableOn_sharpCoPoissonP_sq_Ioi_two
  rw [show Set.Ioc (0 : ℝ) 2 ∪ Set.Ioi 2 = Set.Ioi 0 by
    ext t
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (ht | ht) <;> linarith
    · intro ht
      by_cases h2 : t ≤ 2
      · exact Or.inl ⟨ht, h2⟩
      · exact Or.inr (lt_of_not_ge h2)] at h
  exact h

/-- Critical half-weight fails unconditionally: weighted energy is not integrable. -/
theorem not_integrableOn_sharpCriticalDensity_Ioi_zero :
    ¬ MeasureTheory.IntegrableOn (fun t : ℝ => t * sharpCoPoissonP t ^ 2) (Set.Ioi 0) := by
  intro h
  have htwo : MeasureTheory.IntegrableOn (fun t : ℝ => t * sharpCoPoissonP t ^ 2)
      (Set.Ioi 2) := h.mono_set (Set.Ioi_subset_Ioi (by norm_num))
  have hfinite := MeasureTheory.intervalIntegral_tendsto_integral_Ioi 2 htwo tendsto_id
  change Tendsto sharpCriticalFlux atTop
    (nhds (∫ t in Set.Ioi (2 : ℝ), t * sharpCoPoissonP t ^ 2)) at hfinite
  have hzero := hfinite.div_atTop Real.tendsto_log_atTop
  have heq : (1 / 4 : ℝ) = 0 :=
    tendsto_nhds_unique tendsto_sharpCriticalFlux_div_log hzero
  norm_num at heq


end
end RHTower
