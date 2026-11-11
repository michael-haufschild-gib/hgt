import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheBoxCameraRemainder

/-!
# Uniform prime cost for varying box cameras

Box averaging preserves the pointwise bound one. After rescaling to unit
support the profile is bounded by its radius. The prime mean square thus
costs only `8 T (log T)²`, retaining the depth-centering exponential gain,
uniformly in convolution order.
-/

noncomputable section

open Complex MeasureTheory Set Filter
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

theorem eventually_integral_boxCameraPoly_sq_le
    {A h r c : ℝ} (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r)
    (hc0 : 0 < c) (hc : c < 1 / 3) :
    ∀ᶠ T : ℝ in atTop, ∀ (n : ℕ) (b y : ℝ),
      boxCameraRadius A h n r = c * Real.log T → 0 ≤ b →
      boxCameraRadius A h n r ≤ y →
      y + boxCameraRadius A h n r ≤ (1 - c) * Real.log T →
      (∫ t in T..(2 * T), ‖boxCameraPoly A h n r b y t‖ ^ 2) ≤
        (8 * Real.log T ^ 2 * T) *
          Real.exp (-(2 * b * (y - boxCameraRadius A h n r))) := by
  obtain ⟨CΛ, hCΛ⟩ := exists_sum_vonMangoldt_sq_div_le
  filter_upwards [eventually_ge_atTop 3,
    Real.tendsto_log_atTop.eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop (64 / c ^ 2),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 + |CΛ|)]
    with T hT hL hLd hLC n b y heq hb hy hyT
  have hδ := boxCameraRadius_pos hA hh hr n
  have hy0 : 0 ≤ y + c * Real.log T := by rw [← heq]; linarith only [hδ, hy]
  have hbnd := integral_depthCenteredCameraPoly_sq_le
    (abs_boxTuranProfile_le hA hh hr n) (boxTuranProfile_support hA hh hr n)
    hb hCΛ hc0 hc hT hL hLd hLC hy0 (by rwa [← heq])
  have hcoef : 8 * (boxCameraRadius A h n r) ^ 2 / c ^ 2 * T =
      8 * Real.log T ^ 2 * T := by
    rw [heq]
    field_simp [hc0.ne']
  rw [hcoef, ← heq] at hbnd
  exact hbnd

end GaloisForLFunctions.MultiscaleMollifiedZetaField
