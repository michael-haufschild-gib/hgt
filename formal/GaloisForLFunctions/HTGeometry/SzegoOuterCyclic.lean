import GaloisForLFunctions.HTGeometry.DiskMultiplierOuterFactor
import GaloisForLFunctions.HTGeometry.SmirnovBoundaryQuotient

/-!
# Cyclicity of canonical Szegő outer factors

The reciprocal of the outer factor for the lower-truncated weight is bounded.  Multiplying it by
the original outer factor gives contractive analytic functions whose values at the origin tend to
one.  Their Hardy vectors therefore tend strongly to the constant vector, proving dense range of
multiplication by the original outer factor.
-/

open Complex MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Positive lower truncation of the canonical boundary weight. -/
def diskMultiplierOuterTruncatedWeight
    (phi : DiskMultiplier) (n : ℕ) (theta : ℝ) : ℝ :=
  max (diskMultiplierOuterWeight phi theta) (Real.exp (-(n : ℝ)))

theorem diskMultiplierOuterTruncatedWeight_pos
    (phi : DiskMultiplier) (n : ℕ) (theta : ℝ) :
    0 < diskMultiplierOuterTruncatedWeight phi n theta :=
  lt_of_lt_of_le (diskMultiplierOuterWeight_pos phi theta) (le_max_left _ _)

theorem diskMultiplierOuterTruncatedWeight_lower
    (phi : DiskMultiplier) (n : ℕ) (theta : ℝ) :
    Real.exp (-(n : ℝ)) ≤ diskMultiplierOuterTruncatedWeight phi n theta :=
  le_max_right _ _

theorem diskMultiplierOuterTruncatedWeight_le
    (phi : DiskMultiplier) (n : ℕ) (theta : ℝ) :
    diskMultiplierOuterTruncatedWeight phi n theta ≤ (max 1 phi.bd) ^ 2 := by
  apply max_le
  · exact diskMultiplierOuterWeight_le phi theta
  · have hn : 0 ≤ (n : ℝ) := by positivity
    have hexp : Real.exp (-(n : ℝ)) ≤ 1 := by
      simpa using Real.exp_le_one_iff.mpr (by linarith)
    exact hexp.trans (by nlinarith [le_max_left (1 : ℝ) phi.bd])

theorem diskMultiplierOuterTruncatedWeight_periodic
    (phi : DiskMultiplier) (n : ℕ) :
    Function.Periodic (diskMultiplierOuterTruncatedWeight phi n)
      (2 * Real.pi) := by
  intro theta
  rw [diskMultiplierOuterTruncatedWeight, diskMultiplierOuterTruncatedWeight,
    diskMultiplierOuterWeight_periodic phi theta]

theorem log_diskMultiplierOuterTruncatedWeight
    (phi : DiskMultiplier) (n : ℕ) (theta : ℝ) :
    Real.log (diskMultiplierOuterTruncatedWeight phi n theta) =
      max (Real.log (diskMultiplierOuterWeight phi theta)) (-(n : ℝ)) := by
  rw [diskMultiplierOuterTruncatedWeight]
  by_cases h : diskMultiplierOuterWeight phi theta ≤ Real.exp (-(n : ℝ))
  · rw [max_eq_right h, Real.log_exp]
    have hlog : Real.log (diskMultiplierOuterWeight phi theta) ≤ -(n : ℝ) := by
      rw [← Real.exp_le_exp]
      simpa [Real.exp_log (diskMultiplierOuterWeight_pos phi theta)] using h
    exact (max_eq_right hlog).symm
  · have h' : Real.exp (-(n : ℝ)) ≤ diskMultiplierOuterWeight phi theta := le_of_not_ge h
    rw [max_eq_left h']
    have hlog : -(n : ℝ) ≤ Real.log (diskMultiplierOuterWeight phi theta) := by
      rw [← Real.exp_le_exp]
      simpa [Real.exp_log (diskMultiplierOuterWeight_pos phi theta)] using h'
    exact (max_eq_left hlog).symm

theorem abs_log_diskMultiplierOuterTruncatedWeight_le
    (phi : DiskMultiplier) (n : ℕ) (theta : ℝ) :
    |Real.log (diskMultiplierOuterTruncatedWeight phi n theta)| ≤
      |Real.log (diskMultiplierOuterWeight phi theta)| := by
  rw [log_diskMultiplierOuterTruncatedWeight]
  have hn : 0 ≤ (n : ℝ) := by positivity
  by_cases h : Real.log (diskMultiplierOuterWeight phi theta) ≤ -(n : ℝ)
  · rw [max_eq_right h]
    have hlog : Real.log (diskMultiplierOuterWeight phi theta) ≤ 0 := h.trans (neg_nonpos.mpr hn)
    rw [abs_of_nonpos (neg_nonpos.mpr hn), abs_of_nonpos hlog]
    linarith
  · rw [max_eq_left (le_of_not_ge h)]

theorem intervalIntegrable_log_diskMultiplierOuterTruncatedWeight
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0)
    (n : ℕ) :
    IntervalIntegrable
      (fun theta => Real.log (diskMultiplierOuterTruncatedWeight phi n theta))
      volume 0 (2 * Real.pi) := by
  let f : ℝ → ℝ := fun theta => Real.log (diskMultiplierOuterWeight phi theta)
  let F : ℝ → ℝ := fun theta =>
    Real.log (diskMultiplierOuterTruncatedWeight phi n theta)
  have hf := intervalIntegrable_log_diskMultiplierOuterWeight phi hphi
  have hang : Measurable angularCircle := by
    apply Continuous.measurable
    unfold angularCircle
    fun_prop
  have hw : Measurable (diskMultiplierOuterWeight phi) := by
    exact (((measurable_diskMultiplierBoundarySafe phi).comp hang).norm.pow_const 2)
  have hFm : AEStronglyMeasurable F volume := by
    exact (Real.measurable_log.comp (hw.max measurable_const)).aestronglyMeasurable
  constructor
  · exact hf.1.norm.mono' hFm.restrict
      (Filter.Eventually.of_forall fun theta => by
        simpa [F, f, Real.norm_eq_abs] using
          abs_log_diskMultiplierOuterTruncatedWeight_le phi n theta)
  · exact hf.2.norm.mono' hFm.restrict
      (Filter.Eventually.of_forall fun theta => by
        simpa [F, f, Real.norm_eq_abs] using
          abs_log_diskMultiplierOuterTruncatedWeight_le phi n theta)

theorem normSq_szegoOuter_mono_of_log_le
    {u v : ℝ → ℝ}
    (hlogu : IntervalIntegrable (fun theta => Real.log (u theta)) volume
      0 (2 * Real.pi))
    (hlogv : IntervalIntegrable (fun theta => Real.log (v theta)) volume
      0 (2 * Real.pi))
    (huv : ∀ theta, Real.log (u theta) ≤ Real.log (v theta))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (varphi : ℝ) :
    ‖szegoOuter u (circleMap 0 r varphi)‖ ^ 2 ≤
      ‖szegoOuter v (circleMap 0 r varphi)‖ ^ 2 := by
  rw [normSq_szegoOuter_circleMap hlogu hr0 hr1 varphi,
    normSq_szegoOuter_circleMap hlogv hr0 hr1 varphi]
  apply Real.exp_le_exp.mpr
  gcongr
  have habs : |r| < 1 := by rw [abs_of_nonneg hr0]; exact hr1
  have hcont : Continuous (fun theta => poissonKer r (theta - varphi)) :=
    (poissonKer_continuous habs).comp (continuous_id.sub continuous_const)
  apply intervalIntegral.integral_mono_on (by positivity)
    (hlogu.continuousOn_mul hcont.continuousOn)
    (hlogv.continuousOn_mul hcont.continuousOn)
  intro theta _
  exact mul_le_mul_of_nonneg_left (huv theta)
    (poissonKer_nonneg hr0 hr1 (theta - varphi))

/-- Bounded analytic reciprocal of the lower-truncated outer factor. -/
noncomputable def diskMultiplierOuterTruncatedInverse
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0)
    (n : ℕ) : DiskMultiplier where
  fn := fun z => (szegoOuter (diskMultiplierOuterTruncatedWeight phi n) z)⁻¹
  diff := (analyticOnNhd_inv_szegoOuter
    (intervalIntegrable_log_diskMultiplierOuterTruncatedWeight phi hphi n)).differentiableOn
  bd := Real.exp (n : ℝ)
  bd_nonneg := (Real.exp_pos _).le
  bd_le := by
    intro z hz
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    have hz1 : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    have hsq := normSq_inv_szegoOuter_le_from_weight_lower
      (Real.exp_pos (-(n : ℝ)))
      (intervalIntegrable_log_diskMultiplierOuterTruncatedWeight phi hphi n)
      (diskMultiplierOuterTruncatedWeight_lower phi n)
      hz0 hz1 z.arg
    rw [circleMap_norm_arg, Real.exp_neg, inv_inv] at hsq
    have hexpone : 1 ≤ Real.exp (n : ℝ) :=
      Real.one_le_exp (by positivity)
    nlinarith [norm_nonneg
      ((szegoOuter (diskMultiplierOuterTruncatedWeight phi n) z)⁻¹)]

/-- Contractive quotient of the original outer factor by its lower-truncated outer factor. -/
noncomputable def diskMultiplierOuterCyclicApprox
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0)
    (n : ℕ) : DiskMultiplier where
  fn := fun z => szegoOuter (diskMultiplierOuterWeight phi) z *
    (szegoOuter (diskMultiplierOuterTruncatedWeight phi n) z)⁻¹
  diff := (analyticOnNhd_szegoOuter
    (intervalIntegrable_log_diskMultiplierOuterWeight phi hphi)).differentiableOn.mul
      (analyticOnNhd_inv_szegoOuter
        (intervalIntegrable_log_diskMultiplierOuterTruncatedWeight phi hphi n)).differentiableOn
  bd := 1
  bd_nonneg := zero_le_one
  bd_le := by
    intro z hz
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    have hz1 : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    have hsq := normSq_szegoOuter_mono_of_log_le
      (intervalIntegrable_log_diskMultiplierOuterWeight phi hphi)
      (intervalIntegrable_log_diskMultiplierOuterTruncatedWeight phi hphi n)
      (fun theta => by
        rw [log_diskMultiplierOuterTruncatedWeight]
        exact le_max_left _ _)
      hz0 hz1 z.arg
    rw [circleMap_norm_arg] at hsq
    rw [norm_mul, norm_inv]
    have hnorm := (sq_le_sq₀
      (norm_nonneg (szegoOuter (diskMultiplierOuterWeight phi) z))
      (norm_nonneg (szegoOuter (diskMultiplierOuterTruncatedWeight phi n) z))).mp hsq
    rw [← div_eq_mul_inv]
    exact (div_le_one (norm_pos_iff.mpr (szegoOuter_ne_zero _ _))).mpr hnorm

theorem tendsto_log_diskMultiplierOuterTruncatedWeight
    (phi : DiskMultiplier) (theta : ℝ) :
    Tendsto
      (fun n : ℕ => Real.log (diskMultiplierOuterTruncatedWeight phi n theta))
      atTop (𝓝 (Real.log (diskMultiplierOuterWeight phi theta))) := by
  apply tendsto_const_nhds.congr'
  obtain ⟨N, hN⟩ := exists_nat_ge
    (-Real.log (diskMultiplierOuterWeight phi theta))
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [log_diskMultiplierOuterTruncatedWeight]
  apply max_eq_left
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem tendsto_integral_log_diskMultiplierOuterTruncatedWeight
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    Tendsto
      (fun n : ℕ => ∫ theta in (0 : ℝ)..(2 * Real.pi),
        Real.log (diskMultiplierOuterTruncatedWeight phi n theta))
      atTop
      (𝓝 (∫ theta in (0 : ℝ)..(2 * Real.pi),
        Real.log (diskMultiplierOuterWeight phi theta))) := by
  let f : ℝ → ℝ := fun theta => Real.log (diskMultiplierOuterWeight phi theta)
  let F : ℕ → ℝ → ℝ := fun n theta =>
    Real.log (diskMultiplierOuterTruncatedWeight phi n theta)
  have hang : Measurable angularCircle := by
    apply Continuous.measurable
    unfold angularCircle
    fun_prop
  have hw : Measurable (diskMultiplierOuterWeight phi) :=
    (((measurable_diskMultiplierBoundarySafe phi).comp hang).norm.pow_const 2)
  have hFm : ∀ n, AEStronglyMeasurable (F n)
      (volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))) := by
    intro n
    exact (Real.measurable_log.comp (hw.max measurable_const)).aestronglyMeasurable.restrict
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun theta => |f theta|)
  · exact Filter.Eventually.of_forall hFm
  · exact Filter.Eventually.of_forall fun n =>
      Filter.Eventually.of_forall fun theta _ => by
        simpa [F, f, Real.norm_eq_abs] using
          abs_log_diskMultiplierOuterTruncatedWeight_le phi n theta
  · exact (intervalIntegrable_log_diskMultiplierOuterWeight phi hphi).norm
  · exact Filter.Eventually.of_forall fun theta _ =>
      tendsto_log_diskMultiplierOuterTruncatedWeight phi theta

theorem szegoOuter_zero_eq_real_exp (w : ℝ → ℝ) :
    szegoOuter w 0 =
      ((Real.exp ((1 / (4 * Real.pi)) *
        ∫ theta in (0 : ℝ)..(2 * Real.pi), Real.log (w theta)) : ℝ) : ℂ) := by
  have hint :
      (∫ theta in (0 : ℝ)..(2 * Real.pi),
        -herglotzRieszKernel 0 (circleMap 0 1 theta) 0 *
          (Real.log (w theta) : ℂ)) =
        ((∫ theta in (0 : ℝ)..(2 * Real.pi), Real.log (w theta) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro theta _
    rw [neg_herglotz_zero, one_mul]
  rw [szegoOuter, hint]
  congr 1
  push_cast
  ring

theorem tendsto_szegoOuter_truncated_zero
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    Tendsto
      (fun n : ℕ => szegoOuter (diskMultiplierOuterTruncatedWeight phi n) 0)
      atTop
      (𝓝 (szegoOuter (diskMultiplierOuterWeight phi) 0)) := by
  have hint := tendsto_integral_log_diskMultiplierOuterTruncatedWeight phi hphi
  have hscaled := hint.const_mul (1 / (4 * Real.pi))
  have hexp := (Real.continuous_exp.tendsto _).comp hscaled
  have hcomplex := Complex.continuous_ofReal.tendsto.comp hexp
  simpa only [szegoOuter_zero_eq_real_exp] using hcomplex

end

end GaloisForLFunctions.HTGeometry
