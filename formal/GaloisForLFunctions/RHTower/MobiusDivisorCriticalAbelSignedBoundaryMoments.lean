import GaloisForLFunctions.RHTower.MobiusDivisorCriticalMovingHeadMellin

/-!
# Exact signed boundary moments of the actual critical Abel source

The admitted absolute quadratic log moment permits right differentiation
of the actual Mellin integral at its critical boundary. The simple source
jet identifies its mass as zero and its first logarithmic moment as
minus one third of the divisor harmonic boundary.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

private def abelBoundaryWeight (y : ℝ) : ℝ :=
  criticalContinuousAbel y / y ^ (5 / 2 : ℝ)

private def abelBoundaryMajorant (y : ℝ) : ℝ :=
  |criticalContinuousAbel y| * (1 + Real.log y ^ (2 : ℕ)) / y ^ (5 / 2 : ℝ)

private theorem abelBoundaryWeight_measurable : Measurable abelBoundaryWeight :=
  measurable_criticalContinuousAbel.div (measurable_id.pow_const (5 / 2 : ℝ))

private theorem abelBoundary_weighted_bound {y b : ℝ} (hy : 1 < y)
    (hb : |b| ≤ 1 + Real.log y ^ (2 : ℕ)) :
    ‖abelBoundaryWeight y * b‖ ≤ abelBoundaryMajorant y := by
  have hp : 0 < y ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.norm_eq_abs, abs_mul, abelBoundaryWeight, abs_div, abs_of_pos hp]
  calc
    _ ≤ |criticalContinuousAbel y| / y ^ (5 / 2 : ℝ) *
        (1 + Real.log y ^ (2 : ℕ)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by dsimp [abelBoundaryMajorant]; ring

private theorem abelBoundary_exp_bound {δ y : ℝ} (hδ : 0 ≤ δ) (hy : 1 < y) :
    |Real.exp (-δ * Real.log y)| ≤ 1 + Real.log y ^ (2 : ℕ) := by
  rw [abs_of_pos (Real.exp_pos _)]
  have h := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ) (Real.log_nonneg hy.le))
  nlinarith [sq_nonneg (Real.log y)]

private theorem abelBoundary_exp_integrable {δ : ℝ} (hδ : 0 ≤ δ) :
    IntegrableOn (fun y => abelBoundaryWeight y * Real.exp (-δ * Real.log y))
      (Ioi (1 : ℝ)) := by
  apply integrableOn_criticalContinuousAbel_boundary_log_sq.mono'
    ((abelBoundaryWeight_measurable.mul
      ((measurable_const.mul Real.measurable_log).exp)).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact abelBoundary_weighted_bound hy (abelBoundary_exp_bound hδ hy)

private theorem abelBoundary_exp_eq_mellin (δ : ℝ) :
    (∫ y in Ioi (1 : ℝ), abelBoundaryWeight y * Real.exp (-δ * Real.log y)) =
      criticalSourceRealMellin criticalContinuousAbel δ := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have hy0 : 0 < y := zero_lt_one.trans hy
  have hp : y ^ (-(5 / 2 : ℝ) - δ) =
      1 / y ^ (5 / 2 : ℝ) * Real.exp (-δ * Real.log y) := by
    rw [Real.rpow_def_of_pos hy0, Real.rpow_def_of_pos hy0, one_div,
      ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  change abelBoundaryWeight y * Real.exp (-δ * Real.log y) =
    y ^ (-(5 / 2 : ℝ) - δ) * criticalContinuousAbel y
  rw [hp]
  dsimp [abelBoundaryWeight]
  ring

private theorem abelBoundary_exp_slope_bound {δ y : ℝ} (hδ : 0 < δ) (hy : 1 < y) :
    |(Real.exp (-δ * Real.log y) - 1) / δ| ≤ 1 + Real.log y ^ (2 : ℕ) := by
  have ht : 0 ≤ Real.log y := Real.log_nonneg hy.le
  have he : Real.exp (-δ * Real.log y) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ.le) ht)
  have hs : |(Real.exp (-δ * Real.log y) - 1) / δ| ≤ Real.log y := by
    rw [abs_div, abs_of_pos hδ, abs_of_nonpos (sub_nonpos.mpr he)]
    apply (div_le_iff₀ hδ).mpr
    nlinarith [Real.add_one_le_exp (-δ * Real.log y)]
  exact hs.trans (by nlinarith [sq_nonneg (Real.log y - 1)])

private theorem abelBoundary_exp_slope (y : ℝ) :
    Tendsto (fun δ : ℝ => (Real.exp (-δ * Real.log y) - 1) / δ)
      (𝓝[>] 0) (𝓝 (-Real.log y)) := by
  have h := (((hasDerivAt_id (0 : ℝ)).neg.mul_const (Real.log y)).exp).tendsto_slope_zero_right
  simpa only [Pi.neg_apply, id_eq, zero_add, neg_zero, zero_mul, Real.exp_zero,
    one_mul, neg_mul, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

/-- The first logarithmic boundary moment is an admitted signed source integral. -/
theorem integrableOn_criticalAbel_boundary_log :
    IntegrableOn (fun y : ℝ => criticalContinuousAbel y / y ^ (5 / 2 : ℝ) * Real.log y)
      (Ioi (1 : ℝ)) := by
  apply integrableOn_criticalContinuousAbel_boundary_log_sq.mono'
    ((abelBoundaryWeight_measurable.mul Real.measurable_log).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  apply abelBoundary_weighted_bound hy
  rw [abs_of_nonneg (Real.log_nonneg hy.le)]
  nlinarith [sq_nonneg (Real.log y - 1)]

/-- Actual right derivative of the critical Abel Mellin integral. -/
theorem criticalAbelRealMellin_boundary_right_slope :
    Tendsto (fun δ : ℝ =>
      (criticalSourceRealMellin criticalContinuousAbel δ -
        criticalSourceRealMellin criticalContinuousAbel 0) / δ)
      (𝓝[>] 0) (𝓝 (-(∫ y in Ioi (1 : ℝ),
        criticalContinuousAbel y / y ^ (5 / 2 : ℝ) * Real.log y))) := by
  let F : ℝ → ℝ → ℝ := fun δ y => abelBoundaryWeight y *
    ((Real.exp (-δ * Real.log y) - 1) / δ)
  have hmeas (δ : ℝ) : Measurable (F δ) :=
    abelBoundaryWeight_measurable.mul
      ((((measurable_const.mul Real.measurable_log).exp).sub measurable_const).div measurable_const)
  have hbound : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ᵐ y ∂volume.restrict (Ioi (1 : ℝ)),
      ‖F δ y‖ ≤ abelBoundaryMajorant y := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact abelBoundary_weighted_bound hy (abelBoundary_exp_slope_bound hδ hy)
  have hlim : ∀ᵐ y ∂volume.restrict (Ioi (1 : ℝ)),
      Tendsto (fun δ => F δ y) (𝓝[>] 0) (𝓝 (-(abelBoundaryWeight y * Real.log y))) := by
    filter_upwards with y
    simpa only [F, mul_neg] using (abelBoundary_exp_slope y).const_mul (abelBoundaryWeight y)
  have ht := tendsto_integral_filter_of_dominated_convergence abelBoundaryMajorant
    (Eventually.of_forall (fun δ => (hmeas δ).aestronglyMeasurable.restrict))
    hbound integrableOn_criticalContinuousAbel_boundary_log_sq hlim
  rw [integral_neg] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [← abelBoundary_exp_eq_mellin δ, ← abelBoundary_exp_eq_mellin 0,
    ← integral_sub (abelBoundary_exp_integrable hδ.le) (abelBoundary_exp_integrable le_rfl),
    ← integral_div]
  apply integral_congr_ae
  filter_upwards with y
  simp only [F, neg_zero, zero_mul, Real.exp_zero, mul_one]
  ring

/-- The actual critical Abel boundary has zero total signed mass. -/
theorem criticalAbel_boundary_mass_zero :
    (∫ y in Ioi (1 : ℝ), criticalContinuousAbel y / y ^ (5 / 2 : ℝ)) = 0 := by
  have hδ : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (criticalSourceRealMellin criticalContinuousAbel) (𝓝[>] 0) (𝓝 0) := by
    have h := criticalAbelRealMellin_simpleJet.mul hδ
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact div_mul_cancel₀ _ (ne_of_gt hδ)
  have hc : Tendsto (criticalSourceRealMellin criticalContinuousAbel) (𝓝[>] 0)
      (𝓝 (criticalSourceRealMellin criticalContinuousAbel 0)) := by
    have h := (criticalAbelRealMellin_boundary_right_slope.mul hδ).add_const
      (criticalSourceRealMellin criticalContinuousAbel 0)
    simp only [mul_zero, zero_add] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [div_mul_cancel₀ _ (ne_of_gt hδ)]
    ring
  have he := tendsto_nhds_unique hc hz
  rw [← abelBoundary_exp_eq_mellin 0] at he
  simpa only [neg_zero, zero_mul, Real.exp_zero, mul_one, abelBoundaryWeight] using he

/-- The source's first logarithmic moment has an exact negative value. -/
theorem criticalAbel_boundary_log_moment :
    (∫ y in Ioi (1 : ℝ), criticalContinuousAbel y / y ^ (5 / 2 : ℝ) * Real.log y) =
      -(divisorHarmonicBoundary / 3) := by
  have hz : criticalSourceRealMellin criticalContinuousAbel 0 = 0 := by
    rw [← abelBoundary_exp_eq_mellin 0]
    simpa only [neg_zero, zero_mul, Real.exp_zero, mul_one, abelBoundaryWeight]
      using criticalAbel_boundary_mass_zero
  have h := criticalAbelRealMellin_boundary_right_slope
  simp only [hz, sub_zero] at h
  have he := tendsto_nhds_unique h criticalAbelRealMellin_simpleJet
  linarith

end RHTower
