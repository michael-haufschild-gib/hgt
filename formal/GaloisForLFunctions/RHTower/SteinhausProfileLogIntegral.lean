import GaloisForLFunctions.RHTower.SteinhausRateFunction

/-!
# The logarithmic moment of the weight profile

`∫₀¹ log w_α(v) dv = log(1−α) + α`, the card's `(28)`.  Combined with the sharp upper envelope of
the circle cumulant it gives `Λ_α(λ) ≤ λ − ½log λ + C_α`, which is the deficit that makes the rate
function diverge at `q = 1`.
-/

open MeasureTheory Set

namespace HTGeometry

noncomputable section

theorem integral_log_unit : (∫ v in (0 : ℝ)..1, Real.log v) = -1 := by
  rw [integral_log]
  simp

theorem weightProfile_pos {α : ℝ} (hα : α < 1) {v : ℝ} (hv : 0 < v) : 0 < weightProfile α v := by
  rw [weightProfile]
  have h1 : (0 : ℝ) < 1 - α := by linarith
  have h2 : (0 : ℝ) < v ^ (-α) := Real.rpow_pos_of_pos hv _
  positivity

theorem log_weightProfile {α : ℝ} (hα : α < 1) {v : ℝ} (hv : 0 < v) :
    Real.log (weightProfile α v) = Real.log (1 - α) - α * Real.log v := by
  rw [weightProfile, Real.log_mul (by linarith) (Real.rpow_pos_of_pos hv _).ne',
    Real.log_rpow hv]
  ring

theorem intervalIntegrable_log_weightProfile {α : ℝ} (hα : α < 1) :
    IntervalIntegrable (fun v : ℝ => Real.log (weightProfile α v)) volume 0 1 := by
  have hmain : IntervalIntegrable
      (fun v : ℝ => Real.log (1 - α) - α * Real.log v) volume 0 1 :=
    intervalIntegrable_const.sub (intervalIntegral.intervalIntegrable_log'.const_mul α)
  constructor
  · refine (hmain.1).congr_fun_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact (log_weightProfile hα hv.1).symm
  · have hempty : Set.Ioc (1 : ℝ) 0 = ∅ := Set.Ioc_eq_empty (by norm_num)
    rw [IntegrableOn, hempty]
    simp

/-- **The logarithmic moment of the profile.** -/
theorem integral_log_weightProfile {α : ℝ} (hα : α < 1) :
    (∫ v in (0 : ℝ)..1, Real.log (weightProfile α v)) = Real.log (1 - α) + α := by
  have hcongr : (∫ v in (0 : ℝ)..1, Real.log (weightProfile α v))
      = ∫ v in (0 : ℝ)..1, (Real.log (1 - α) - α * Real.log v) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with v hmem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Ioc] at hmem
    exact log_weightProfile hα hmem.1
  rw [hcongr, intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegral.intervalIntegrable_log'.const_mul α),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_log_unit]
  simp

theorem log_sqrt_pi_div {x : ℝ} (hx : 0 < x) :
    Real.log (Real.sqrt (Real.pi / (2 * x)))
      = (Real.log Real.pi - Real.log 2 - Real.log x) / 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [Real.log_sqrt (by positivity), Real.log_div hpi.ne' (by positivity),
    Real.log_mul (by norm_num) hx.ne']
  ring

/-- **The cumulant deficit.**  `Λ_α(λ) ≤ λ − ½log λ + C_α`. -/
theorem rvCumulant_le_sub_half_log {α : ℝ} (hα : α < 1) {lam : ℝ} (hlam : 0 < lam) :
    rvCumulant α lam
      ≤ lam - Real.log lam / 2
        + (Real.log Real.pi - Real.log 2 - Real.log (1 - α) - α) / 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set C : ℝ := (Real.log Real.pi - Real.log 2 - Real.log lam) / 2 with hC
  have hmaj : IntervalIntegrable
      (fun v : ℝ => lam * weightProfile α v + (C - Real.log (weightProfile α v) / 2))
      volume 0 1 :=
    ((intervalIntegrable_weightProfile hα).const_mul lam).add
      (intervalIntegrable_const.sub
        ((intervalIntegrable_log_weightProfile hα).div_const 2))
  have hae : ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      steinhausLogLaplace (lam * weightProfile α v)
        ≤ lam * weightProfile α v + (C - Real.log (weightProfile α v) / 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hw : 0 < weightProfile α v := weightProfile_pos hα hv.1
    have hx : 0 < lam * weightProfile α v := by positivity
    have hbound := steinhausLogLaplace_le hx
    rw [log_sqrt_pi_div hx, Real.log_mul hlam.ne' hw.ne'] at hbound
    refine hbound.trans (le_of_eq ?_)
    rw [hC]
    ring
  have hae' : (fun v => steinhausLogLaplace (lam * weightProfile α v))
      ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
        fun v => lam * weightProfile α v + (C - Real.log (weightProfile α v) / 2) := by
    rw [← MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc]
    exact hae
  have hmono := intervalIntegral.integral_mono_ae_restrict (by norm_num : (0:ℝ) ≤ 1)
    (intervalIntegrable_rvCumulant_integrand hα lam) hmaj hae'
  rw [rvCumulant]
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_add ((intervalIntegrable_weightProfile hα).const_mul lam)
      (intervalIntegrable_const.sub ((intervalIntegrable_log_weightProfile hα).div_const 2)),
    intervalIntegral.integral_const_mul, integral_weightProfile hα,
    intervalIntegral.integral_sub intervalIntegrable_const
      ((intervalIntegrable_log_weightProfile hα).div_const 2),
    intervalIntegral.integral_const, intervalIntegral.integral_div,
    integral_log_weightProfile hα, hC]
  ring

/-- **The rate function diverges at `q = 1`.** -/
theorem le_rvRate_log {α : ℝ} (hα : α < 1) {q : ℝ} (hq : q < 1) :
    Real.log (1 / (1 - q)) / 2 - 1
        - (Real.log Real.pi - Real.log 2 - Real.log (1 - α) - α) / 2
      ≤ rvRate α q := by
  have hq1 : (0 : ℝ) < 1 - q := by linarith
  set lam : ℝ := 1 / (1 - q) with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  have hbound := rvCumulant_le_sub_half_log hα hlam
  have hle := le_rvRate hα hq hlam.le
  have hid : lam * q - lam = -1 := by
    rw [hlamdef]
    field_simp
    ring
  linarith [hle, hbound, hid]

/-- **The rate function tends to infinity at the boundary `q = 1`.**  This is part `3` of the
card's theorem. -/
theorem tendsto_rvRate_atTop {α : ℝ} (hα : α < 1) :
    Filter.Tendsto (rvRate α) (nhdsWithin 1 (Set.Iio (1 : ℝ))) Filter.atTop := by
  set C : ℝ := (Real.log Real.pi - Real.log 2 - Real.log (1 - α) - α) / 2 with hC
  have hsub : Filter.Tendsto (fun q : ℝ => 1 - q) (nhdsWithin 1 (Set.Iio (1 : ℝ)))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Filter.Tendsto (fun q : ℝ => 1 - q) (nhds 1) (nhds (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with q hq
      simpa using hq
  have hinv : Filter.Tendsto (fun q : ℝ => (1 - q)⁻¹) (nhdsWithin 1 (Set.Iio (1 : ℝ)))
      Filter.atTop := tendsto_inv_nhdsGT_zero.comp hsub
  have hlogt : Filter.Tendsto (fun q : ℝ => Real.log ((1 - q)⁻¹))
      (nhdsWithin 1 (Set.Iio (1 : ℝ))) Filter.atTop := Real.tendsto_log_atTop.comp hinv
  have hdiv : Filter.Tendsto (fun q : ℝ => Real.log ((1 - q)⁻¹) / 2)
      (nhdsWithin 1 (Set.Iio (1 : ℝ))) Filter.atTop := hlogt.atTop_div_const (by norm_num)
  have hlog : Filter.Tendsto (fun q : ℝ => Real.log ((1 - q)⁻¹) / 2 - 1 - C)
      (nhdsWithin 1 (Set.Iio (1 : ℝ))) Filter.atTop := by
    have h1 := Filter.tendsto_atTop_add_const_right _ (-1 - C) hdiv
    exact h1.congr fun q => by ring
  refine Filter.tendsto_atTop_mono' _ ?_ hlog
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq1 : q < 1 := hq
  have hb := le_rvRate_log hα hq1
  rw [one_div] at hb
  exact hb

end

end HTGeometry
