import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Smooth compactly supported functions have rapidly decaying transforms

A smooth compactly supported function is Schwartz, so its Fourier transform is Schwartz, so it
decays faster than every power.  This is the quantitative form of "no finite Rees order sees an
essential phase": an oscillatory integral against a fixed smooth compactly supported weight beats
every polynomial rate in the frequency.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter SchwartzMap
open scoped Topology FourierTransform ContDiff

/-- **Rapid decay.**  The Fourier transform of a smooth compactly supported function beats every
polynomial rate. -/
theorem tendsto_pow_mul_norm_fourier_atTop
    {g : ℝ → ℂ} (hsupp : HasCompactSupport g) (hsmooth : ContDiff ℝ ∞ g) (N : ℕ) :
    Tendsto (fun w : ℝ => w ^ N * ‖𝓕 g w‖) atTop (𝓝 0) := by
  set G : 𝓢(ℝ, ℂ) := hsupp.toSchwartzMap hsmooth with hG
  have hFG := SchwartzMap.fourier_coe G
  obtain ⟨C, hCpos, hC⟩ := (𝓕 G).decay (N + 1) 0
  have hbound : ∀ w : ℝ, 0 < w → w ^ N * ‖𝓕 g w‖ ≤ C / w := by
    intro w hw
    have hkey : w ^ (N + 1) * ‖(𝓕 G) w‖ ≤ C := by
      have h := hC w
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_pos hw] at h
      exact h
    have hval : 𝓕 g w = (𝓕 G) w := (congrFun hFG w).symm
    rw [hval, le_div_iff₀ hw]
    calc w ^ N * ‖(𝓕 G) w‖ * w = w ^ (N + 1) * ‖(𝓕 G) w‖ := by ring
      _ ≤ C := hkey
  refine squeeze_zero' ?_ ?_ (Filter.Tendsto.const_div_atTop tendsto_id C)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
    exact hbound w hw

/-- **Rapid decay in the negative direction.** -/
theorem tendsto_pow_mul_norm_fourier_neg_atTop
    {g : ℝ → ℂ} (hsupp : HasCompactSupport g) (hsmooth : ContDiff ℝ ∞ g) (N : ℕ) :
    Tendsto (fun w : ℝ => w ^ N * ‖𝓕 g (-w)‖) atTop (𝓝 0) := by
  set G : 𝓢(ℝ, ℂ) := hsupp.toSchwartzMap hsmooth with hG
  have hFG := SchwartzMap.fourier_coe G
  obtain ⟨C, hCpos, hC⟩ := (𝓕 G).decay (N + 1) 0
  have hbound : ∀ w : ℝ, 0 < w → w ^ N * ‖𝓕 g (-w)‖ ≤ C / w := by
    intro w hw
    have hkey : w ^ (N + 1) * ‖(𝓕 G) (-w)‖ ≤ C := by
      have h := hC (-w)
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_neg, abs_of_pos hw] at h
      exact h
    have hval : 𝓕 g (-w) = (𝓕 G) (-w) := (congrFun hFG (-w)).symm
    rw [hval, le_div_iff₀ hw]
    calc w ^ N * ‖(𝓕 G) (-w)‖ * w = w ^ (N + 1) * ‖(𝓕 G) (-w)‖ := by ring
      _ ≤ C := hkey
  refine squeeze_zero' ?_ ?_ (Filter.Tendsto.const_div_atTop tendsto_id C)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
    exact hbound w hw

end RHTower
