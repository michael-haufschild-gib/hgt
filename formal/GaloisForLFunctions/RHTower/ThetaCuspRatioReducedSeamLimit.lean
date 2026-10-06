import GaloisForLFunctions.RHTower.ThetaCuspRatioReducedSeamIdentity
import GaloisForLFunctions.RHTower.ThetaCuspRatioReducedDeterminantTransport

namespace RHTower.ThetaCuspUpperSeam
noncomputable section
set_option autoImplicit false
open scoped ContDiff
open Filter Topology MvPolynomial
open HTGeometry.ThetaRatioWeightedSquare HTGeometry.ThetaRatioInfinity
open ThetaCuspModularRatio ThetaCuspOddDirectionTransport

private theorem continuous_scaledUpperA_at_zero : ContinuousAt scaledUpperA 0 := by
  have ha : ContDiff ℝ ∞ (deriv (normalizedBase (10000000000000:ℝ))) := by
    simpa using (normalizedBase_regular (10000000000000:ℝ)).1.iterate_deriv 1
  have hl : ContDiff ℝ ∞ (deriv (ThetaCuspHeadGrowth.centerDrive (10000000000000:ℝ))) := by
    simpa using (centerDrive_smooth (10000000000000:ℝ)).iterate_deriv 1
  exact (continuousAt_dslope_same.mpr (ha.differentiable (by simp) 0)).add
    (((continuousAt_dslope_same.mpr (hasDerivAt_shearGap 0).differentiableAt).mul
      hl.continuous.continuousAt).div_const 4)

private theorem continuous_scaledB_at_zero : ContinuousAt scaledB 0 := by
  have hb : ContDiff ℝ ∞ (deriv normalizedB) := by
    simpa using normalizedB_regular.1.iterate_deriv 1
  exact continuousAt_dslope_same.mpr (hb.differentiable (by simp) 0)

private theorem continuous_scaledD_at_zero : ContinuousAt scaledD 0 := by
  have hd : ContDiff ℝ ∞ (deriv normalizedD) := by
    simpa using normalizedD_regular.1.iterate_deriv 1
  exact continuousAt_dslope_same.mpr (hd.differentiable (by simp) 0)

theorem scaledUpperDeterminant_continuousAt_zero :
    ContinuousAt scaledUpperDeterminant 0 :=
  (continuous_scaledUpperA_at_zero.mul continuous_scaledD_at_zero).sub
    (continuous_scaledB_at_zero.pow 2)

theorem scaledUpperDeterminant_zero_pos : 0 < scaledUpperDeterminant 0 :=
  scaled_seam_signs.2

theorem center_over_drift_tendsto_seam :
    Tendsto (fun x : ℝ => x/u x) (𝓝[>] 0) (𝓝 ((9*k 0)⁻¹)) := by
  have hu0 : u 0=0 := by simp [u]
  have hk0 : 0 < k 0 := by linarith [k_gt (show (0:ℝ)≤0 by rfl)]
  have hd : dslope u 0 0=9*k 0 := by
    rw [dslope_same,(du (show (0:ℝ)≤0 by rfl)).deriv]
    simp only [t,hu0,zero_pow (by omega : (2:ℕ)≠0),sub_zero]
    ring
  have hc : ContinuousAt (dslope u 0) 0 :=
    continuousAt_dslope_same.mpr (du (show (0:ℝ)≤0 by rfl)).differentiableAt
  have ht : Tendsto (dslope u 0) (𝓝[>] 0) (𝓝 (9*k 0)) := by
    rw [←hd]
    exact hc.mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from inf_le_left)
  have hi := ht.inv₀ (show 9*k 0≠0 by positivity)
  apply hi.congr'
  filter_upwards [show ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x from self_mem_nhdsWithin] with x hx
  rw [dslope_of_ne u hx.ne',slope_def_field,hu0,sub_zero,sub_zero,inv_div]

def reducedSeamNormalizerLimit : ℝ := (6:ℝ)^30*(k 0-1/6)^7/(9*k 0)

theorem reducedSeamNormalizer_tendsto :
    Tendsto reducedSeamNormalizer (𝓝[>] 0) (𝓝 reducedSeamNormalizerLimit) := by
  have hk : Tendsto k (𝓝[>] 0) (𝓝 (k 0)) :=
    (dk (show (0:ℝ)≤0 by rfl)).continuousAt.mono_left
      (show 𝓝[>] (0:ℝ)≤𝓝 0 from inf_le_left)
  have h : Tendsto (fun x : ℝ => (6:ℝ)^30*(k x-1/6)^7*(x/u x))
      (𝓝[>] 0) (𝓝 ((6:ℝ)^30*(k 0-1/6)^7*(9*k 0)⁻¹)) :=
    (tendsto_const_nhds.mul ((hk.sub tendsto_const_nhds).pow 7)).mul
      center_over_drift_tendsto_seam
  unfold reducedSeamNormalizer
  simpa only [reducedSeamNormalizerLimit,div_eq_mul_inv] using h

theorem reducedSeamNormalizerLimit_pos : 0 < reducedSeamNormalizerLimit := by
  have hk : 0 < k 0-1/6 := by linarith [k_gt (show (0:ℝ)≤0 by rfl)]
  have hk0 : 0 < k 0 := by linarith
  unfold reducedSeamNormalizerLimit
  positivity

def upperDeterminantSeamLimit : ℝ :=
  reducedSeamNormalizerLimit^2*scaledUpperDeterminant 0

theorem upperDeterminantSeamLimit_pos : 0 < upperDeterminantSeamLimit :=
  mul_pos (pow_pos reducedSeamNormalizerLimit_pos 2) scaledUpperDeterminant_zero_pos

theorem actual_reduced_upper_determinant_tendsto_seam :
    Tendsto (fun x => (eval (actualSquarePoint x)
      (upperDeterminantCore (10000000000000:ℂ))).re)
      (𝓝[>] 0) (𝓝 upperDeterminantSeamLimit) := by
  have hd : Tendsto scaledUpperDeterminant (𝓝[>] 0) (𝓝 (scaledUpperDeterminant 0)) :=
    scaledUpperDeterminant_continuousAt_zero.mono_left
      (show 𝓝[>] (0:ℝ)≤𝓝 0 from inf_le_left)
  have h := (reducedSeamNormalizer_tendsto.pow 2).mul hd
  apply h.congr'
  filter_upwards [show ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x from self_mem_nhdsWithin] with x hx
  exact (actual_reduced_determinant_seam_real hx).symm

theorem actual_reduced_upper_determinant_pos_near_seam :
    ∀ᶠ x in 𝓝[>] (0:ℝ), 0 < (eval (actualSquarePoint x)
      (upperDeterminantCore (10000000000000:ℂ))).re :=
  actual_reduced_upper_determinant_tendsto_seam.eventually_const_lt
    upperDeterminantSeamLimit_pos

theorem actual_upper_determinant_pos_near_seam :
    ∀ᶠ x in 𝓝[>] (0:ℝ), 0 < (eval (actualSquarePoint x)
      (upperCenterDeterminant (10000000000000:ℂ))).re := by
  filter_upwards [actual_reduced_upper_determinant_pos_near_seam,
    show ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x from self_mem_nhdsWithin] with x hp hx
  rw [actual_upper_determinant_core_identity]
  exact mul_pos (pow_pos (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)) 52) hp

end
end RHTower.ThetaCuspUpperSeam
