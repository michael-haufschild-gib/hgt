import GaloisForLFunctions.BiScaleUncertainty.CompensatedPhysicalLogarithmicProducer

/-!
# Strong convergence of compact logarithmic producers

The explicit truncation, zero-integral compensation and box smoothing converge
in physical L² to the positive component. The same sequence converges uniformly
on bounded logarithmic intervals and in every compact source and jump form.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology CompactlySupported ENNReal NNReal

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear

set_option autoImplicit false

theorem producerScale_tendsto : Tendsto producerScale atTop atTop := by
  exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

theorem producerAlpha_tendsto : Tendsto producerAlpha atTop (𝓝 0) := by
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp producerScale_tendsto)

theorem producerBeta_tendsto : Tendsto producerBeta atTop atTop :=
  Real.tendsto_exp_atTop.comp producerScale_tendsto

private def truncationErrorDensity (n : ℕ) (q : Velocity) (t : ℝ) : ℝ :=
  ((Ioc (producerAlpha n) (producerBeta n)).indicator (q : ℝ → ℝ) t -
    (Ioi (0 : ℝ)).indicator (q : ℝ → ℝ) t) ^ 2

private theorem truncationErrorDensity_le (n : ℕ) (q : Velocity) (t : ℝ) :
    ‖truncationErrorDensity n q t‖ ≤ (q t) ^ 2 := by
  unfold truncationErrorDensity
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  by_cases ht : t ∈ Ioc (producerAlpha n) (producerBeta n)
  · have hp : t ∈ Ioi (0 : ℝ) := lt_trans (producerAlpha_pos n) ht.1
    rw [indicator_of_mem ht, indicator_of_mem hp, sub_self, sq, zero_mul]
    exact sq_nonneg (q t)
  · rw [indicator_of_notMem ht]
    by_cases hp : t ∈ Ioi (0 : ℝ)
    · simp only [indicator_of_mem hp, zero_sub, neg_sq, le_refl]
    · rw [indicator_of_notMem hp, sub_self, sq, zero_mul]
      exact sq_nonneg (q t)

private theorem truncationErrorDensity_tendsto (q : Velocity) (t : ℝ) :
    Tendsto (fun n => truncationErrorDensity n q t) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  by_cases ht : 0 < t
  · filter_upwards [producerAlpha_tendsto.eventually (gt_mem_nhds ht),
      producerBeta_tendsto.eventually_ge_atTop t] with n ha hb
    simp only [truncationErrorDensity, indicator_of_mem (show
      t ∈ Ioc (producerAlpha n) (producerBeta n) from ⟨ha, hb⟩),
      indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht), sub_self, sq, zero_mul]
  · exact Eventually.of_forall fun n => by
      have hn : t ∉ Ioc (producerAlpha n) (producerBeta n) :=
        fun h => ht (lt_trans (producerAlpha_pos n) h.1)
      simp only [truncationErrorDensity, indicator_of_notMem hn,
        indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht), sub_self, sq, zero_mul]

private theorem norm_sq_truncation_error (n : ℕ) (q : Velocity) :
    ‖truncatedVelocity n q - positivePhysicalVelocity q‖ ^ 2 =
      ∫ t, truncationErrorDensity n q t := by
  rw [norm_sq_velocity]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (truncatedVelocity n q) (positivePhysicalVelocity q),
    ae_physicalIntervalRestriction (producerAlpha n) (producerBeta n) q,
    ae_positivePhysicalVelocity q] with t hs hr hp
  simp only [Pi.sub_apply] at hs
  rw [hs]
  change (physicalIntervalRestriction (producerAlpha n) (producerBeta n) q t -
    positivePhysicalVelocity q t) ^ 2 = _
  rw [hr, hp]
  rfl

/-- Interval truncation converges to the visible positive physical velocity. -/
theorem truncatedVelocity_tendsto (q : Velocity) :
    Tendsto (fun n => truncatedVelocity n q) atTop (𝓝 (positivePhysicalVelocity q)) := by
  have hi : Tendsto (fun n => ∫ t, truncationErrorDensity n q t) atTop (𝓝 0) := by
    simpa only [Pi.pow_apply, Pi.sub_apply, truncationErrorDensity, integral_zero] using
      tendsto_integral_of_dominated_convergence (fun t => (q t) ^ 2)
        (fun n => (((Lp.memLp q).aestronglyMeasurable.indicator measurableSet_Ioc).sub
          ((Lp.memLp q).aestronglyMeasurable.indicator measurableSet_Ioi)).pow 2)
        (integrable_velocity_sq q)
        (fun n => Eventually.of_forall (truncationErrorDensity_le n q))
        (Eventually.of_forall (truncationErrorDensity_tendsto q))
  have hs : Tendsto (fun n => ‖truncatedVelocity n q - positivePhysicalVelocity q‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [norm_sq_truncation_error] using hi
  have hn : Tendsto (fun n => ‖truncatedVelocity n q - positivePhysicalVelocity q‖)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hs
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

private theorem producerHalfDecay_tendsto :
    Tendsto (fun n => Real.exp (-producerScale n / 2)) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  simpa only [Function.comp_def, neg_div] using tendsto_neg_atTop_atBot.comp
    (Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2) producerScale_tendsto)

/-- The explicit compensator disappears in physical L². -/
theorem compensatorVelocity_tendsto (q : Velocity) :
    Tendsto (fun n => compensatorVelocity n q) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun n => Real.exp (-producerScale n / 2) * ‖q‖) atTop (𝓝 0) from by
      simpa only [zero_mul] using producerHalfDecay_tendsto.mul_const ‖q‖)
  · exact fun n => norm_nonneg _
  · exact fun n => norm_compensatorVelocity_le n q

theorem compensatedVelocity_tendsto (q : Velocity) :
    Tendsto (fun n => compensatedVelocity n q) atTop (𝓝 (positivePhysicalVelocity q)) := by
  simpa only [compensatedVelocity, sub_zero] using
    (truncatedVelocity_tendsto q).sub (compensatorVelocity_tendsto q)

private theorem producerSmoothingParameter_tendsto :
    Tendsto (fun n => -2 * producerScale n) atTop atBot := by
  simpa only [Function.comp_def, neg_mul] using tendsto_neg_atTop_atBot.comp
    (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) producerScale_tendsto)

/-- Compactly supported smoothed producers converge to the positive component of every velocity. -/
theorem smoothedCompensatedVelocity_tendsto (q : Velocity) :
    Tendsto (fun n => smoothedCompensatedVelocity n q) atTop
      (𝓝 (positivePhysicalVelocity q)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun n => ‖truncatedVelocity n q - positivePhysicalVelocity q‖)
      atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp (truncatedVelocity_tendsto q)
  have hc : Tendsto (fun n => Real.exp (-producerScale n / 2) * ‖q‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using producerHalfDecay_tendsto.mul_const ‖q‖
  have hb : Tendsto (fun n => ‖physicalBoxAverage (-2 * producerScale n)
      (positivePhysicalVelocity q) - positivePhysicalVelocity q‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp
      ((physicalBoxAverage_tendsto (positivePhysicalVelocity q)).comp
        producerSmoothingParameter_tendsto)
  have hh := (ht.add hc).add hb
  simp only [add_zero] at hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
    (fun _ => norm_nonneg _) (fun n => norm_smoothedCompensatedVelocity_sub_positive_le n q)

/-- The logarithmic trace is bounded by the physical energy up to its endpoint. -/
theorem logPrimitive_sq_le_exp_mul_norm_sq (q : Velocity) (x : ℝ) :
    (logPrimitive q x) ^ 2 ≤ Real.exp x * ‖q‖ ^ 2 := by
  have hp : primitive q 0 = 0 := by simp only [primitive, intervalIntegral.integral_same]
  have ht := increment_sq_le_energy q 0 ⟨Real.exp x, (Real.exp_pos x).le⟩
  simp only [zero_add, hp, sub_zero] at ht
  have he : energy q 0 (Real.exp x) ≤ ‖q‖ ^ 2 := by
    rw [energy, intervalIntegral.integral_of_le (Real.exp_pos x).le, norm_sq_velocity]
    exact setIntegral_le_integral (integrable_velocity_sq q)
      (Eventually.of_forall fun t => sq_nonneg (q t))
  exact ht.trans (mul_le_mul_of_nonneg_left he (Real.exp_pos x).le)

theorem logPrimitive_sub_positive (u q : Velocity) (x : ℝ) :
    logPrimitive (u - positivePhysicalVelocity q) x = logPrimitive u x - logPrimitive q x := by
  simp only [logPrimitive, primitive_sub_velocity,
    primitive_positivePhysicalVelocity q (Real.exp x) (Real.exp_pos x).le]

/-- A single physical norm error controls all logarithmic traces to the left of `b`. -/
theorem abs_logPrimitive_sub_le (u q : Velocity) {x b : ℝ} (hx : x ≤ b) :
    |logPrimitive u x - logPrimitive q x| ≤
      Real.exp (b / 2) * ‖u - positivePhysicalVelocity q‖ := by
  have hs := logPrimitive_sq_le_exp_mul_norm_sq (u - positivePhysicalVelocity q) x
  rw [logPrimitive_sub_positive] at hs
  have he : Real.exp x * ‖u - positivePhysicalVelocity q‖ ^ 2 ≤
      Real.exp b * ‖u - positivePhysicalVelocity q‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hx) (sq_nonneg _)
  have hb : (Real.exp (b / 2) * ‖u - positivePhysicalVelocity q‖) ^ 2 =
      Real.exp b * ‖u - positivePhysicalVelocity q‖ ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  have hn : 0 ≤ Real.exp (b / 2) * ‖u - positivePhysicalVelocity q‖ := by positivity
  nlinarith only [hs, he, hb, sq_abs (logPrimitive u x - logPrimitive q x),
    abs_nonneg (logPrimitive u x - logPrimitive q x), hn]

/-- The actual smoothed logarithmic states are continuously differentiable. -/
theorem contDiff_smoothedLogarithmicState (n : ℕ) (q : Velocity) :
    ContDiff ℝ 1 (smoothedLogarithmicState n q) :=
  contDiff_one_iff_deriv.mpr ⟨fun x => (hasDerivAt_smoothedLogarithmicState n q x).differentiableAt,
    continuous_deriv_smoothedLogarithmicState n q⟩

theorem hasCompactSupport_smoothedLogarithmicState (n : ℕ) (q : Velocity) :
    HasCompactSupport (smoothedLogarithmicState n q) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := Real.log (producerAlpha n - producerStep n))
      (b := Real.log (producerUpper n)))
  intro x hx
  have hn := Function.mem_support.mp hx
  constructor
  · by_contra h
    exact hn (smoothedLogarithmicState_eq_zero_of_le n q (le_of_not_ge h))
  · by_contra h
    exact hn (smoothedLogarithmicState_eq_zero_of_upper_le n q (le_of_not_ge h))

/-- The same explicit state packaged as a compactly supported continuous function. -/
def compactSmoothedLogarithmicState (n : ℕ) (q : Velocity) : C_c(ℝ, ℝ) :=
  ⟨⟨smoothedLogarithmicState n q, (contDiff_smoothedLogarithmicState n q).continuous⟩,
    hasCompactSupport_smoothedLogarithmicState n q⟩

/-- Uniform convergence holds even on each entire left half-line. -/
theorem smoothedLogarithmicState_tendstoUniformlyOn (q : Velocity) (b : ℝ) :
    TendstoUniformlyOn (fun n => smoothedLogarithmicState n q) (logPrimitive q)
      atTop (Iic b) := by
  have hn : Tendsto (fun n => ‖smoothedCompensatedVelocity n q - positivePhysicalVelocity q‖)
      atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (smoothedCompensatedVelocity_tendsto q)
  have hb : Tendsto (fun n => Real.exp (b / 2) *
      ‖smoothedCompensatedVelocity n q - positivePhysicalVelocity q‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using hn.const_mul (Real.exp (b / 2))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hb.eventually (gt_mem_nhds hε)] with n hn x hx
  rw [Real.dist_eq, abs_sub_comm]
  exact (abs_logPrimitive_sub_le (smoothedCompensatedVelocity n q) q hx).trans_lt hn

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear

namespace GaloisForLFunctions.BiScaleUncertainty.PathCongestion

open SobolevShear

set_option autoImplicit false

/-- Exact compact-source coefficient for the physical trace estimate. -/
def sourceTraceCoefficient (ψ : C_c(ℝ, ℝ)) : ℝ := ∫ x, ψ x ^ 2 * Real.exp x

theorem integrable_sourceTraceCoefficient (ψ : C_c(ℝ, ℝ)) :
    Integrable (fun x => ψ x ^ 2 * Real.exp x) := by
  apply ((ψ.continuous.pow 2).mul Real.continuous_exp).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact ψ.hasCompactSupport.isCompact
  intro x hx
  apply subset_closure
  apply Function.mem_support.mpr
  intro hz
  apply (Function.mem_support.mp hx)
  change ψ x ^ 2 * Real.exp x = 0
  rw [hz, sq, zero_mul, zero_mul]

theorem sourceTraceCoefficient_nonneg (ψ : C_c(ℝ, ℝ)) : 0 ≤ sourceTraceCoefficient ψ :=
  integral_nonneg fun x => mul_nonneg (sq_nonneg _) (Real.exp_pos x).le

/-- Compact source mass is bounded by its explicit trace coefficient times physical energy. -/
theorem sourceMass_le_traceCoefficient (ψ : C_c(ℝ, ℝ)) (q : Velocity) :
    sourceMass ψ q 0 ≤ ENNReal.ofReal (sourceTraceCoefficient ψ * ‖q‖ ^ 2) := by
  calc
    sourceMass ψ q 0 ≤ ∫⁻ x, ENNReal.ofReal ((ψ x ^ 2 * Real.exp x) * ‖q‖ ^ 2) := by
      apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      simp only [zero_add]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (logPrimitive_sq_le_exp_mul_norm_sq q x) (sq_nonneg (ψ x))
    _ = ENNReal.ofReal (sourceTraceCoefficient ψ * ‖q‖ ^ 2) := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        ((integrable_sourceTraceCoefficient ψ).mul_const (‖q‖ ^ 2))
        (Eventually.of_forall fun x => by positivity), integral_mul_const]
      rfl

theorem sourceMass_sub_eq_sub_positivePhysicalVelocity (ψ : C_c(ℝ, ℝ)) (u q : Velocity) :
    sourceMass ψ (u - q) 0 = sourceMass ψ (u - positivePhysicalVelocity q) 0 := by
  apply lintegral_congr
  intro x
  simp only [zero_add, logPrimitive, primitive_sub_velocity,
    primitive_positivePhysicalVelocity q (Real.exp x) (Real.exp_pos x).le]

/-- Source-mass error retains the exact coefficient `∫ ψ² exp`. -/
theorem sourceMass_smoothedCompensatedVelocity_sub_le (ψ : C_c(ℝ, ℝ)) (q : Velocity) (n : ℕ) :
    sourceMass ψ (smoothedCompensatedVelocity n q - q) 0 ≤
      ENNReal.ofReal (sourceTraceCoefficient ψ *
        ‖smoothedCompensatedVelocity n q - positivePhysicalVelocity q‖ ^ 2) := by
  rw [sourceMass_sub_eq_sub_positivePhysicalVelocity]
  exact sourceMass_le_traceCoefficient ψ _

/-- Every constructed compact source form sees the actual approximation error tend to zero. -/
theorem compact_formError_smoothedCompensatedVelocity_tendsto
    (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0) (q : Velocity) :
    Tendsto (fun n => sourceMass ψ (smoothedCompensatedVelocity n q - q) 0 +
      jumpEnergy (compactMixture ψ weights) (smoothedCompensatedVelocity n q - q))
      atTop (𝓝 0) := by
  have he : Tendsto (fun n => ‖smoothedCompensatedVelocity n q - positivePhysicalVelocity q‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [sq, zero_mul] using
      (tendsto_iff_norm_sub_tendsto_zero.mp (smoothedCompensatedVelocity_tendsto q)).pow 2
  have hc : Tendsto (fun n => ENNReal.ofReal ((sourceTraceCoefficient ψ +
      (resistanceMass ψ weights).toReal) *
      ‖smoothedCompensatedVelocity n q - positivePhysicalVelocity q‖ ^ 2)) atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (he.const_mul
        (sourceTraceCoefficient ψ + (resistanceMass ψ weights).toReal))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun _ => zero_le)
  intro n
  calc
    _ ≤ ENNReal.ofReal (sourceTraceCoefficient ψ *
          ‖smoothedCompensatedVelocity n q - positivePhysicalVelocity q‖ ^ 2) +
        resistanceMass ψ weights *
          ENNReal.ofReal (‖smoothedCompensatedVelocity n q - positivePhysicalVelocity q‖ ^ 2) :=
      add_le_add (sourceMass_smoothedCompensatedVelocity_sub_le ψ q n)
        (compact_jumpEnergy_smoothedCompensatedVelocity_sub_le ψ weights n q)
    _ = _ := by
      dsimp only
      rw [add_mul, ENNReal.ofReal_add (mul_nonneg (sourceTraceCoefficient_nonneg ψ) (sq_nonneg _))
        (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)),
        ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (resistanceMass_ne_top ψ weights)]

end GaloisForLFunctions.BiScaleUncertainty.PathCongestion
