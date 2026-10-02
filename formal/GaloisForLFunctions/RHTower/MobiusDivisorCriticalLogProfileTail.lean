import GaloisForLFunctions.RHTower.MobiusDivisorCriticalLogProfilePrimitive
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Vanishing quadratic tail of the actual log profile

Finite source primitives and absolute velocity moments identify the
profile with a tail integral. This proves the pointwise decay needed by
the prime-tail asymptotic without a Tauberian converse.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

private theorem logProfile_integrable :
    IntegrableOn criticalAbelLogProfile (Ioi (0 : ℝ)) := by
  apply integrableOn_criticalAbelLogProfile_quadratic.norm.mono'
    measurable_criticalAbelLogProfile.aestronglyMeasurable.restrict
  filter_upwards with t
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 + t ^ (2 : ℕ))]
  nlinarith [abs_nonneg (criticalAbelLogProfile t), sq_nonneg t]

private theorem logVelocity_square_integrable :
    IntegrableOn (fun t : ℝ => t ^ (2 : ℕ) * |criticalAbelLogVelocity t|)
      (Ioi (0 : ℝ)) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ (2 : ℕ) * criticalAbelLogVelocity t)
      (Ioi (0 : ℝ)) := by
    apply IntegrableOn.congr_fun
      (integrableOn_criticalAbelLogVelocity_quadratic.sub integrableOn_criticalAbelLogVelocity)
      _ measurableSet_Ioi
    intro t _
    dsimp only [Pi.sub_apply]
    ring
  apply IntegrableOn.congr_fun hi.norm _ measurableSet_Ioi
  intro t _
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]

/-- The actual velocity has zero total mass: its primitive has a limit,
and admission of that primitive forces the limit to vanish. -/
theorem criticalAbelLogVelocity_mass_zero :
    (∫ t in Ioi (0 : ℝ), criticalAbelLogVelocity t) = 0 := by
  have hlim : Tendsto criticalAbelLogProfile atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), criticalAbelLogVelocity t)) := by
    apply (intervalIntegral_tendsto_integral_Ioi 0
      integrableOn_criticalAbelLogVelocity tendsto_id).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact criticalAbelLogVelocity_integral ht
  have hi : IntegrableAtFilter criticalAbelLogProfile atTop volume :=
    ⟨Ioi (0 : ℝ), Ioi_mem_atTop _, logProfile_integrable⟩
  apply hi.eq_zero_of_tendsto _ hlim
  intro s hs
  obtain ⟨b, hb⟩ := mem_atTop_sets.mp hs
  rw [← top_le_iff, ← Real.volume_Ici (a := b)]
  exact measure_mono hb

/-- Exact tail representation of the physical log profile. -/
theorem criticalAbelLogProfile_eq_velocity_tail {t : ℝ} (ht : 0 ≤ t) :
    criticalAbelLogProfile t = -(∫ u in Ioi t, criticalAbelLogVelocity u) := by
  have h := intervalIntegral.integral_interval_add_Ioi integrableOn_criticalAbelLogVelocity
    (integrableOn_criticalAbelLogVelocity.mono_set (Ioi_subset_Ioi ht))
  rw [criticalAbelLogVelocity_integral ht, criticalAbelLogVelocity_mass_zero] at h
  linarith

private theorem logProfile_square_tail_bound {t : ℝ} (ht : 0 ≤ t) :
    |t ^ (2 : ℕ) * criticalAbelLogProfile t| ≤
      ∫ u in Ioi t, u ^ (2 : ℕ) * |criticalAbelLogVelocity u| := by
  have hv := integrableOn_criticalAbelLogVelocity.mono_set (Ioi_subset_Ioi ht)
  have hw := logVelocity_square_integrable.mono_set (Ioi_subset_Ioi ht)
  rw [criticalAbelLogProfile_eq_velocity_tail ht, abs_mul,
    abs_of_nonneg (sq_nonneg t), abs_neg]
  calc
    _ ≤ t ^ (2 : ℕ) * (∫ u in Ioi t, |criticalAbelLogVelocity u|) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg t)
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := volume.restrict (Ioi t)) criticalAbelLogVelocity
    _ = ∫ u in Ioi t, t ^ (2 : ℕ) * |criticalAbelLogVelocity u| :=
      (integral_const_mul _ _).symm
    _ ≤ _ := by
      apply integral_mono_ae (hv.norm.const_mul (t ^ (2 : ℕ))) hw
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      change t < u at hu
      have hsq : t ^ (2 : ℕ) ≤ u ^ (2 : ℕ) := by nlinarith
      exact mul_le_mul_of_nonneg_right hsq (abs_nonneg _)

/-- Pointwise quadratic decay follows from the actual source tail, not
from its Mellin jet. -/
theorem tendsto_criticalAbelLogProfile_quadratic_zero :
    Tendsto (fun t : ℝ => t ^ (2 : ℕ) * criticalAbelLogProfile t) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) _
    (tendsto_integral_Ioi_zero (f := fun u : ℝ => u ^ (2 : ℕ) * |criticalAbelLogVelocity u|)
      (μ := volume) tendsto_id)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simpa only [Real.norm_eq_abs, id_eq] using logProfile_square_tail_bound ht

end RHTower
