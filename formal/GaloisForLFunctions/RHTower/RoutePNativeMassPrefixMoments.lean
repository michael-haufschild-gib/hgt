import GaloisForLFunctions.RHTower.RoutePNativeMassCompensation

/-!
# The signed mass restored by causal native compensation

The actual zero-mass profile has an integrable causal mass primitive.
Its total mass is the positive divisor boundary divided by three. Hence
adding a nonzero multiple of this primitive changes the source's zeroth
moment; it is not a moment-preserving modification of the full ray.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace RHTower

private theorem mass_deriv (t : ℝ) :
    HasDerivAt routePNativeMassPrefix (criticalAbelLogProfile t) t :=
  intervalIntegral.integral_hasDerivAt_right
    (continuous_criticalAbelLogProfile.intervalIntegrable _ _)
    continuous_criticalAbelLogProfile.aestronglyMeasurable.stronglyMeasurableAtFilter
    continuous_criticalAbelLogProfile.continuousAt

theorem continuous_routePNativeMassPrefix : Continuous routePNativeMassPrefix :=
  (show Differentiable ℝ routePNativeMassPrefix from
    fun t => (mass_deriv t).differentiableAt).continuous

private def massBudget : ℝ :=
  ∫ t in Ioi (0 : ℝ), (1 + t ^ 2) * |criticalAbelLogProfile t|

private theorem quadratic_admission :
    IntegrableOn (fun t : ℝ => (1 + t ^ 2) * |criticalAbelLogProfile t|) (Ioi 0) := by
  apply IntegrableOn.congr_fun integrableOn_criticalAbelLogProfile_quadratic.norm _ measurableSet_Ioi
  intro t _
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + t ^ 2)]

private theorem mass_bound {T : ℝ} (hT : 0 ≤ T) :
    (1 + T ^ 2) * |routePNativeMassPrefix T| ≤ massBudget := by
  have ha := integrable_criticalAbelLogProfile.integrableOn (s := Ioi T)
  have hw := quadratic_admission.mono_set (Ioi_subset_Ioi hT)
  rw [routePNativeMassPrefix_eq_neg_tail, abs_neg]
  calc
    _ ≤ (1 + T ^ 2) * ∫ t in Ioi T, |criticalAbelLogProfile t| := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := volume.restrict (Ioi T)) criticalAbelLogProfile
    _ = ∫ t in Ioi T, (1 + T ^ 2) * |criticalAbelLogProfile t| :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ t in Ioi T, (1 + t ^ 2) * |criticalAbelLogProfile t| := by
      apply integral_mono_ae (ha.norm.const_mul _) hw
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change T < t at ht
      exact mul_le_mul_of_nonneg_right (by nlinarith [ht, hT]) (abs_nonneg _)
    _ ≤ massBudget := by
      exact setIntegral_mono_set quadratic_admission
        (Eventually.of_forall (fun t => by positivity))
        (Eventually.of_forall (fun _ ht => lt_of_le_of_lt hT ht))

/-- Absolute admission of the actual signed mass primitive. -/
theorem integrableOn_routePNativeMassPrefix :
    IntegrableOn routePNativeMassPrefix (Ioi 0) := by
  apply ((integrable_inv_one_add_sq.integrableOn (s := Ioi (0 : ℝ))).const_mul
    massBudget).mono' continuous_routePNativeMassPrefix.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr
  simpa only [mul_comm] using mass_bound (le_of_lt ht)

/-- The terminal term in native first-moment integration by parts vanishes. -/
theorem tendsto_mul_routePNativeMassPrefix_zero :
    Tendsto (fun T : ℝ => T * routePNativeMassPrefix T) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => massBudget / T) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.const_mul massBudget)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hT0 : 0 < T := by linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hT0, le_div_iff₀ hT0]
  have hb := mass_bound hT0.le
  nlinarith [abs_nonneg (routePNativeMassPrefix T)]

private theorem first_admission :
    IntegrableOn (fun t : ℝ => t * criticalAbelLogProfile t) (Ioi 0) := by
  apply quadratic_admission.mono'
    (measurable_id.mul measurable_criticalAbelLogProfile).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖t * criticalAbelLogProfile t‖ ≤ (1 + t ^ 2) * |criticalAbelLogProfile t|
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos ht]
  exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (t - 1)]) (abs_nonneg _)

private theorem finite_mass_identity (T : ℝ) :
    (∫ t in (0 : ℝ)..T, routePNativeMassPrefix t) +
      (∫ t in (0 : ℝ)..T, t * criticalAbelLogProfile t) = T * routePNativeMassPrefix T := by
  have hd (t : ℝ) : HasDerivAt (fun u => u * routePNativeMassPrefix u)
      (routePNativeMassPrefix t + t * criticalAbelLogProfile t) t := by
    simpa only [Pi.mul_def, id_eq, one_mul] using (hasDerivAt_id t).mul (mass_deriv t)
  have hc : Continuous (fun t : ℝ => t * criticalAbelLogProfile t) :=
    continuous_id.mul continuous_criticalAbelLogProfile
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((continuous_routePNativeMassPrefix.add hc).intervalIntegrable 0 T)
  rw [intervalIntegral.integral_add
    (continuous_routePNativeMassPrefix.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)] at h
  simpa only [zero_mul, sub_zero] using h

/-- The exact nonzero mass exposed by the native source's first moment. -/
theorem integral_routePNativeMassPrefix :
    (∫ t in Ioi (0 : ℝ), routePNativeMassPrefix t) = divisorHarmonicBoundary / 3 := by
  have hlim := (intervalIntegral_tendsto_integral_Ioi 0
    integrableOn_routePNativeMassPrefix tendsto_id).add
      (intervalIntegral_tendsto_integral_Ioi 0 first_admission tendsto_id)
  have hzero : Tendsto (fun T : ℝ =>
      (∫ t in (0 : ℝ)..T, routePNativeMassPrefix t) +
        ∫ t in (0 : ℝ)..T, t * criticalAbelLogProfile t) atTop (𝓝 0) :=
    tendsto_mul_routePNativeMassPrefix_zero.congr
      (fun T => (finite_mass_identity T).symm)
  have h := tendsto_nhds_unique hlim hzero
  rw [criticalAbelLogProfile_first_moment] at h
  linarith

def routePNativeMassCompensatedLogProfile (lam t : ℝ) : ℝ :=
  criticalAbelLogProfile t + lam * routePNativeMassPrefix t

/-- Complete admission and exact mass of the compensated native log source.
Every source ingredient is discharged unconditionally. -/
theorem routePNativeMassCompensatedLogProfile_admission_mass (lam : ℝ) :
    IntegrableOn (routePNativeMassCompensatedLogProfile lam) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), routePNativeMassCompensatedLogProfile lam t) =
        lam * (divisorHarmonicBoundary / 3) := by
  have ha := integrable_criticalAbelLogProfile.integrableOn (s := Ioi (0 : ℝ))
  have hm := integrableOn_routePNativeMassPrefix.const_mul lam
  refine ⟨ha.add hm, ?_⟩
  change (∫ t in Ioi (0 : ℝ), criticalAbelLogProfile t + lam * routePNativeMassPrefix t) = _
  rw [integral_add ha hm, integral_const_mul,
    criticalAbelLogProfile_mass_zero, integral_routePNativeMassPrefix, zero_add]

end RHTower
