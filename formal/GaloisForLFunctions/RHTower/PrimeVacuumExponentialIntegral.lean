import GaloisForLFunctions.RHTower.PrimeVacuumCurrent

/-!
# The vacuum constant is the exponential integral

The continuous prime vacuum `V(z) = ∫_e^∞ t^{-z}/log t dt` is the exponential integral
`E₁(z-1)`.  The identification is proved by differentiation in the cut: both
`y ↦ ∫_y^∞ t^{-z}/log t dt` and `y ↦ ∫_{log y}^∞ e^{-(z-1)u}/u du` have derivative
`-y^{-z}/log y` and vanish at infinity.
-/

namespace RHTower

open MeasureTheory Set Filter Topology

noncomputable section

/-- The exponential integral `E₁(s) = ∫_a^∞ e^{-su}/u du`, cut at `a`. -/
def expIntegralOneC (s : ℂ) (a : ℝ) : ℂ := ∫ u in Ioi a, Complex.exp (-s * u) / u

theorem norm_expIntegrand {s : ℂ} {u : ℝ} (hu : 0 < u) :
    ‖Complex.exp (-s * (u : ℂ)) / (u : ℂ)‖ = Real.exp (-s.re * u) / u := by
  rw [norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg hu.le]
  congr 1
  simp

theorem integrableOn_expIntegrand {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => Complex.exp (-s * (u : ℂ)) / (u : ℂ)) (Ioi a) volume := by
  have hbase : IntegrableOn (fun u : ℝ => Real.exp (-s.re * u)) (Ioi a) volume :=
    exp_neg_integrableOn_Ioi a hs
  have hmajor : IntegrableOn (fun u : ℝ => Real.exp (-s.re * u) * a⁻¹) (Ioi a) volume :=
    hbase.mul_const _
  refine Integrable.mono' hmajor ?_ ?_
  · refine (Measurable.div ?_ Complex.measurable_ofReal).aestronglyMeasurable.restrict
    exact Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := lt_trans ha hu
    rw [norm_expIntegrand hu0]
    have hinv : (u : ℝ)⁻¹ ≤ a⁻¹ := inv_anti₀ ha hu.le
    calc Real.exp (-s.re * u) / u = Real.exp (-s.re * u) * u⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp (-s.re * u) * a⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le


theorem continuousAt_expIntegrand {s : ℂ} {u : ℝ} (hu : 0 < u) :
    ContinuousAt (fun t : ℝ => Complex.exp (-s * (t : ℂ)) / (t : ℂ)) u := by
  refine ContinuousAt.div ?_ ?_ (by simpa using ne_of_gt hu)
  · exact Complex.continuous_exp.continuousAt.comp
      ((continuous_const.mul Complex.continuous_ofReal).continuousAt)
  · exact Complex.continuous_ofReal.continuousAt

theorem hasDerivAt_expIntegralOneC {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (expIntegralOneC s) (-(Complex.exp (-s * (a : ℂ)) / (a : ℂ))) a := by
  refine hasDerivAt_integral_Ioi (c := a / 2) (by linarith)
    (integrableOn_expIntegrand hs (by linarith : (0:ℝ) < a / 2)) ?_
    (continuousAt_expIntegrand ha)
  refine ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi ?_ a ha
  intro t ht
  exact (continuousAt_expIntegrand ht).continuousWithinAt

theorem norm_expIntegralOneC_le {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    ‖expIntegralOneC s a‖ ≤ a⁻¹ * ∫ u in Ioi (0 : ℝ), Real.exp (-s.re * u) := by
  have hbase0 : IntegrableOn (fun u : ℝ => Real.exp (-s.re * u)) (Ioi (0 : ℝ)) volume :=
    exp_neg_integrableOn_Ioi 0 hs
  have hbase : IntegrableOn (fun u : ℝ => Real.exp (-s.re * u)) (Ioi a) volume :=
    exp_neg_integrableOn_Ioi a hs
  have hmajor : IntegrableOn (fun u : ℝ => a⁻¹ * Real.exp (-s.re * u)) (Ioi a) volume := by
    have h2 : IntegrableOn (fun u : ℝ => Real.exp (-s.re * u) * a⁻¹) (Ioi a) volume :=
      hbase.mul_const a⁻¹
    have heq : (fun u : ℝ => Real.exp (-s.re * u) * a⁻¹)
        = fun u : ℝ => a⁻¹ * Real.exp (-s.re * u) := by
      funext u; ring
    rwa [heq] at h2
  have hb : ‖expIntegralOneC s a‖ ≤ ∫ u in Ioi a, a⁻¹ * Real.exp (-s.re * u) := by
    rw [expIntegralOneC]
    refine norm_integral_le_of_norm_le hmajor ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := lt_trans ha hu
    rw [norm_expIntegrand hu0]
    have hinv : (u : ℝ)⁻¹ ≤ a⁻¹ := inv_anti₀ ha hu.le
    calc Real.exp (-s.re * u) / u = Real.exp (-s.re * u) * u⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp (-s.re * u) * a⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le
      _ = a⁻¹ * Real.exp (-s.re * u) := by ring
  refine hb.trans ?_
  rw [MeasureTheory.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine MeasureTheory.setIntegral_mono_set hbase0 ?_ ?_
  · filter_upwards with u
    exact (Real.exp_pos _).le
  · exact Filter.Eventually.of_forall (fun u hu => lt_trans ha hu)

theorem tendsto_expIntegralOneC {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun a : ℝ => expIntegralOneC s a) atTop (𝓝 0) := by
  set M : ℝ := ∫ u in Ioi (0 : ℝ), Real.exp (-s.re * u) with hM
  have hmaj : Tendsto (fun a : ℝ => a⁻¹ * M) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.mul_const M
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  exact norm_expIntegralOneC_le hs ha

theorem cpow_eq_exp_ofReal_log {y : ℝ} (hy : 0 < y) (w : ℂ) :
    (y : ℂ) ^ w = Complex.exp (w * (Real.log y : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by simpa using ne_of_gt hy), ← Complex.ofReal_log hy.le,
    mul_comm]

theorem hasDerivAt_expIntegralOneC_log {z : ℂ} (hz : 1 < z.re) {y : ℝ} (hy : 1 < y) :
    HasDerivAt (fun t : ℝ => expIntegralOneC (z - 1) (Real.log t)) (-logPowerTail z 1 y) y := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos hy
  have hsre : (0 : ℝ) < (z - 1).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hg := hasDerivAt_expIntegralOneC hsre hlogy
  have hf : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log (ne_of_gt hy0)
  have hcomp := hg.scomp y hf
  refine hcomp.congr_deriv ?_
  have hexp : Complex.exp (-(z - 1) * (Real.log y : ℂ)) = (y : ℂ) ^ (1 - z) := by
    rw [cpow_eq_exp_ofReal_log hy0]
    congr 1
    ring
  have hyc : (y : ℂ) ≠ 0 := by simpa using ne_of_gt hy0
  have hlogc : ((Real.log y : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hlogy
  have hsplit : (y : ℂ) ^ (1 - z) = (y : ℂ) ^ (-z) * (y : ℂ) := by
    rw [show (1 : ℂ) - z = -z + 1 by ring, Complex.cpow_add _ _ hyc]
    simp
  rw [Complex.real_smul, hexp, hsplit, logPowerTail, pow_one]
  push_cast
  field_simp

/-- **Card equation (20c).**  The continuous prime vacuum is the exponential integral:
`∫_y^∞ t^{-z}/log t dt = E₁((z-1) log y)` in the cut form. -/
theorem primeVacuumTail_eq_expIntegralOneC {z : ℂ} (hz : 1 < z.re) {y : ℝ} (hy : 1 < y) :
    primeVacuumTail z y = expIntegralOneC (z - 1) (Real.log y) := by
  have hsre : (0 : ℝ) < (z - 1).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hlim : Tendsto (fun t : ℝ => expIntegralOneC (z - 1) (Real.log t)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (tendsto_expIntegralOneC hsre).comp Real.tendsto_log_atTop
  have hconst : ∀ Y : ℝ, y ≤ Y →
      primeVacuumTail z Y - expIntegralOneC (z - 1) (Real.log Y)
        = primeVacuumTail z y - expIntegralOneC (z - 1) (Real.log y) := by
    intro Y hY
    have hderiv : ∀ t ∈ uIcc y Y,
        HasDerivAt (fun u : ℝ => primeVacuumTail z u
          - expIntegralOneC (z - 1) (Real.log u)) 0 t := by
      intro t ht
      rw [Set.uIcc_of_le hY] at ht
      have ht1 : 1 < t := lt_of_lt_of_le hy ht.1
      have hFd : HasDerivAt (primeVacuumTail z) (-logPowerTail z 1 t) t := by
        refine hasDerivAt_integral_Ioi (c := (1 + t) / 2) (by linarith)
          (integrableOn_logPowerTail (by linarith : (1:ℝ) < (1 + t) / 2) hz) ?_
          (continuousAt_logPowerTail ht1)
        refine ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi ?_ t ht1
        intro r hr
        exact (continuousAt_logPowerTail hr).continuousWithinAt
      have h := hFd.sub (hasDerivAt_expIntegralOneC_log hz ht1)
      exact h.congr_deriv (by ring)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (intervalIntegrable_const (c := (0 : ℂ)))
    simp only [intervalIntegral.integral_zero] at hFTC
    linear_combination -hFTC
  have hlimD : Tendsto (fun Y : ℝ => primeVacuumTail z Y
      - expIntegralOneC (z - 1) (Real.log Y)) atTop (𝓝 0) := by
    simpa using (tendsto_primeVacuumTail hz).sub hlim
  have hconstlim : Tendsto (fun Y : ℝ => primeVacuumTail z Y
      - expIntegralOneC (z - 1) (Real.log Y)) atTop
      (𝓝 (primeVacuumTail z y - expIntegralOneC (z - 1) (Real.log y))) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop y] with Y hY
    exact (hconst Y hY).symm
  have := tendsto_nhds_unique hconstlim hlimD
  linear_combination this

/-- **Card equation (20c), value form.**  `V(z) = E₁(z-1)`. -/
theorem primeVacuumValue_eq {z : ℂ} (hz : 1 < z.re) :
    primeVacuumValue z = expIntegralOneC (z - 1) 1 := by
  rw [primeVacuumValue, primeVacuumTail_eq_expIntegralOneC hz one_lt_exp_one, Real.log_exp]

end

end RHTower
