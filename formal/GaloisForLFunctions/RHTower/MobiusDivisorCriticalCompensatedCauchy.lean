import GaloisForLFunctions.RHTower.MobiusDivisorCriticalLogProfile

/-!
# Signed main term of the moving prime-tail kernel

Subtract the exact zero-mass term inside the integrand before taking its
norm. A fixed source majorant then admits dominated convergence, giving
the negative first moment as the exact asymptotic coefficient.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

private def compensatedCauchy (t v : ℝ) : ℝ :=
  ((if v ≤ t / 2 then t ^ (2 : ℕ) / (t - v) else 0) - t) * criticalAbelLogProfile v

private def cauchyMajorant (v : ℝ) : ℝ :=
  2 * (1 + v ^ (2 : ℕ)) * |criticalAbelLogProfile v|

private theorem cauchyMajorant_integrable : IntegrableOn cauchyMajorant (Ioi (0 : ℝ)) := by
  apply IntegrableOn.congr_fun (integrableOn_criticalAbelLogProfile_quadratic.norm.const_mul 2)
    _ measurableSet_Ioi
  intro v _
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 1 + v ^ (2 : ℕ)), cauchyMajorant]
  ring

private theorem profile_integrable : IntegrableOn criticalAbelLogProfile (Ioi (0 : ℝ)) := by
  apply integrableOn_criticalAbelLogProfile_quadratic.norm.mono'
    measurable_criticalAbelLogProfile.aestronglyMeasurable.restrict
  filter_upwards with v
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 + v ^ (2 : ℕ))]
  nlinarith [abs_nonneg (criticalAbelLogProfile v), sq_nonneg v]

private theorem compensatedCauchy_measurable (t : ℝ) : Measurable (compensatedCauchy t) := by
  have hm : Measurable (fun v : ℝ => if v ≤ t / 2 then t ^ (2 : ℕ) / (t - v) else 0) :=
    Measurable.ite measurableSet_Iic
      (measurable_const.div (measurable_const.sub measurable_id)) measurable_const
  exact (hm.sub_const t).mul measurable_criticalAbelLogProfile

private theorem compensatedCauchy_bound {t v : ℝ} (ht : 1 ≤ t) (hv : 0 < v) :
    ‖compensatedCauchy t v‖ ≤ cauchyMajorant v := by
  have hcoef : |(if v ≤ t / 2 then t ^ (2 : ℕ) / (t - v) else 0) - t| ≤ 2 * v := by
    by_cases h : v ≤ t / 2
    · have hd : 0 < t - v := by linarith
      have he : t ^ (2 : ℕ) / (t - v) - t = t * v / (t - v) := by
        field_simp [ne_of_gt hd]
        ring
      rw [if_pos h, he, abs_of_nonneg (by positivity)]
      apply (div_le_iff₀ hd).mpr
      nlinarith
    · rw [if_neg h, zero_sub, abs_neg, abs_of_nonneg (by linarith : 0 ≤ t)]
      linarith
  have hvb : 2 * v ≤ 2 * (1 + v ^ (2 : ℕ)) := by nlinarith [sq_nonneg (v - 1)]
  simpa only [compensatedCauchy, Real.norm_eq_abs, abs_mul, cauchyMajorant] using
    mul_le_mul_of_nonneg_right (hcoef.trans hvb) (abs_nonneg (criticalAbelLogProfile v))

private theorem compensatedCauchy_integrable {t : ℝ} (ht : 1 ≤ t) :
    IntegrableOn (compensatedCauchy t) (Ioi (0 : ℝ)) := by
  apply cauchyMajorant_integrable.mono' (compensatedCauchy_measurable t).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact compensatedCauchy_bound ht hv

private theorem compensatedCauchy_limit (v : ℝ) :
    Tendsto (fun t : ℝ => compensatedCauchy t v) atTop (𝓝 (v * criticalAbelLogProfile v)) := by
  have hd : Tendsto (fun t : ℝ => t - v) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-v) tendsto_id
  have h : Tendsto (fun t : ℝ => v + v ^ (2 : ℕ) / (t - v)) atTop (𝓝 v) := by
    simpa using (tendsto_const_nhds (x := v)).add
      ((tendsto_const_nhds (x := v ^ (2 : ℕ))).div_atTop hd)
  apply (h.mul_const (criticalAbelLogProfile v)).congr'
  filter_upwards [eventually_ge_atTop (max 1 (2 * v + 1))] with t ht
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have htv : 2 * v + 1 ≤ t := (le_max_right _ _).trans ht
  have hd0 : t - v ≠ 0 := by linarith
  dsimp [compensatedCauchy]
  rw [if_pos (by linarith : v ≤ t / 2)]
  congr 1
  field_simp [hd0]
  ring

private theorem compensatedCauchy_integral {t : ℝ} (ht : 1 ≤ t) :
    (∫ v in Ioi (0 : ℝ), compensatedCauchy t v) =
      t ^ (2 : ℕ) * ∫ v in (0 : ℝ)..t / 2, criticalAbelLogProfile v / (t - v) := by
  have h : (∫ v in Ioi (0 : ℝ), compensatedCauchy t v) +
      t * (∫ v in Ioi (0 : ℝ), criticalAbelLogProfile v) =
      t ^ (2 : ℕ) * ∫ v in (0 : ℝ)..t / 2, criticalAbelLogProfile v / (t - v) := by
    rw [← integral_const_mul, ← integral_add (compensatedCauchy_integrable ht)
      (profile_integrable.const_mul t)]
    calc
      _ = ∫ v in Ioi (0 : ℝ), t ^ (2 : ℕ) *
          (Iic (t / 2)).indicator (fun v => criticalAbelLogProfile v / (t - v)) v := by
        apply integral_congr_ae
        filter_upwards with v
        by_cases hv : v ≤ t / 2
        · simp only [compensatedCauchy, Set.indicator_apply, mem_Iic, if_pos hv]
          ring
        · simp only [compensatedCauchy, Set.indicator_apply, mem_Iic, if_neg hv]
          ring
      _ = _ := by
        rw [integral_const_mul, integral_indicator measurableSet_Iic,
          Measure.restrict_restrict measurableSet_Iic]
        have hs : Iic (t / 2) ∩ Ioi (0 : ℝ) = Ioc 0 (t / 2) := by
          ext v
          simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_Ioc, and_comm]
        rw [hs, intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ t / 2)]
  simpa only [criticalAbelLogProfile_mass_zero, mul_zero, add_zero] using h

/-- Exact negative asymptotic coefficient of the compensated moving Cauchy
main term. The discrete prime-error term is a separate obligation. -/
theorem tendsto_criticalAbelLogProfile_cauchy_main :
    Tendsto (fun t : ℝ => t ^ (2 : ℕ) *
      ∫ v in (0 : ℝ)..t / 2, criticalAbelLogProfile v / (t - v))
      atTop (𝓝 (-(divisorHarmonicBoundary / 3))) := by
  have hbound : ∀ᶠ t : ℝ in atTop, ∀ᵐ v ∂volume.restrict (Ioi (0 : ℝ)),
      ‖compensatedCauchy t v‖ ≤ cauchyMajorant v := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact compensatedCauchy_bound ht hv
  have h := tendsto_integral_filter_of_dominated_convergence cauchyMajorant
    (Eventually.of_forall (fun t => (compensatedCauchy_measurable t).aestronglyMeasurable.restrict))
    hbound cauchyMajorant_integrable (Eventually.of_forall compensatedCauchy_limit)
  rw [criticalAbelLogProfile_first_moment] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  exact compensatedCauchy_integral ht

end RHTower
