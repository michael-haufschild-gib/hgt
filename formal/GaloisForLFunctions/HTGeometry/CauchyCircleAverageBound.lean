import Mathlib

/-!
# The Cauchy circle-average bound

For `h` holomorphic on the disc `|w - c| < R₂` and continuous on its closure, every point `z` with
`|z - c| ≤ R < R₂` satisfies

  `|h(z)| ≤ (R₂ / (R₂ - R)) · (1/2π) ∫₀^{2π} |h(c + R₂ e^{iθ})| dθ`,

by Cauchy's integral formula and `|c + R₂ e^{iθ} - z| ≥ R₂ - R`.
-/

open Complex Real MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Cauchy circle-average bound.** -/
theorem norm_le_circle_average {h : ℂ → ℂ} {c : ℂ} {R R₂ : ℝ} (hR : 0 ≤ R) (hRR : R < R₂)
    (hd : DiffContOnCl ℂ h (ball c R₂)) {z : ℂ} (hz : dist z c ≤ R) :
    ‖h z‖ ≤ R₂ / (R₂ - R) / (2 * π) * ∫ θ in (0 : ℝ)..2 * π, ‖h (circleMap c R₂ θ)‖ := by
  have hR₂ : 0 < R₂ := by linarith
  have hzb : z ∈ ball c R₂ := by rw [mem_ball]; linarith
  have hcauchy := hd.circleIntegral_sub_inv_smul hzb
  have hcont : Continuous fun θ : ℝ => h (circleMap c R₂ θ) := by
    have hcl := hd.continuousOn
    rw [closure_ball c hR₂.ne'] at hcl
    exact hcl.comp_continuous (continuous_circleMap c R₂)
      (fun θ => sphere_subset_closedBall (circleMap_mem_sphere c hR₂.le θ))
  have hdist : ∀ θ : ℝ, R₂ - R ≤ ‖circleMap c R₂ θ - z‖ := by
    intro θ
    have h1 : ‖circleMap c R₂ θ - c‖ = R₂ := by
      rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hR₂]
    have h2 : ‖z - c‖ ≤ R := by rw [← dist_eq_norm]; exact hz
    have := norm_sub_norm_le (circleMap c R₂ θ - c) (z - c)
    rw [h1, show circleMap c R₂ θ - c - (z - c) = circleMap c R₂ θ - z by ring] at this
    linarith
  have hpt : ∀ θ : ℝ, ‖deriv (circleMap c R₂) θ • ((circleMap c R₂ θ - z)⁻¹ • h (circleMap c R₂ θ))‖ ≤
      R₂ / (R₂ - R) * ‖h (circleMap c R₂ θ)‖ := by
    intro θ
    rw [norm_smul, norm_smul, deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one,
      abs_of_pos hR₂, norm_inv]
    have hpos : 0 < R₂ - R := by linarith
    have hinv : ‖circleMap c R₂ θ - z‖⁻¹ ≤ (R₂ - R)⁻¹ := inv_anti₀ hpos (hdist θ)
    calc R₂ * (‖circleMap c R₂ θ - z‖⁻¹ * ‖h (circleMap c R₂ θ)‖)
        ≤ R₂ * ((R₂ - R)⁻¹ * ‖h (circleMap c R₂ θ)‖) := by gcongr
      _ = R₂ / (R₂ - R) * ‖h (circleMap c R₂ θ)‖ := by ring
  have hbound : 2 * π * ‖h z‖ ≤ R₂ / (R₂ - R) * ∫ θ in (0 : ℝ)..2 * π, ‖h (circleMap c R₂ θ)‖ := by
    have hnorm : ‖(2 * π * I : ℂ) • h z‖ = 2 * π * ‖h z‖ := by
      rw [norm_smul]; simp [abs_of_pos Real.pi_pos]
    rw [← hnorm, ← hcauchy]
    unfold circleIntegral
    refine (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by positivity) ?_ ?_ (fun θ _ => hpt θ)
    · refine Continuous.intervalIntegrable ?_ _ _
      have hne : ∀ θ : ℝ, circleMap c R₂ θ - z ≠ 0 := fun θ h0 => by
        have := hdist θ; rw [h0, norm_zero] at this; linarith
      simp_rw [deriv_circleMap]
      exact ((by fun_prop : Continuous fun θ : ℝ => circleMap 0 R₂ θ * I).smul
        ((((continuous_circleMap c R₂).sub continuous_const).inv₀ hne).smul hcont)).norm
    · exact (continuous_const.mul hcont.norm).intervalIntegrable _ _
  have h2π : 0 < 2 * π := by positivity
  calc ‖h z‖ = (2 * π * ‖h z‖) / (2 * π) := by field_simp
    _ ≤ (R₂ / (R₂ - R) * ∫ θ in (0 : ℝ)..2 * π, ‖h (circleMap c R₂ θ)‖) / (2 * π) := by gcongr
    _ = R₂ / (R₂ - R) / (2 * π) * ∫ θ in (0 : ℝ)..2 * π, ‖h (circleMap c R₂ θ)‖ := by ring

end

end GaloisForLFunctions.HTGeometry
