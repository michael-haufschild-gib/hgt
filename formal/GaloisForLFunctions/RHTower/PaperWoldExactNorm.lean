import GaloisForLFunctions.RHTower.PaperWoldHardySharpness
import GaloisForLFunctions.RHTower.PaperWoldCompositeNormValues
import GaloisForLFunctions.RHTower.PaperWoldHardyMaskedTransport

/-! # Exact critical norms and the complete strict-half norm discontinuity

The Hardy and literal composite operators both have norm and compact-ideal
distance one. Every strict-half difference has exactly that same norm.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry

theorem paperWoldHardyOperator_norm : ‖paperWoldHardyOperator‖ = 1 := by
  apply le_antisymm paperWoldHardyOperator_norm_le_one
  simpa only [ZeroMemClass.coe_zero, sub_zero] using paperWoldHardyOperator_sub_compact_norm_ge_one 0

theorem paperWoldHardyOperator_compactIdealDistance :
    compactIdealDistance paperWoldHardyOperator = 1 := by
  apply le_antisymm
  · simpa only [sub_zero, paperWoldHardyOperator_norm] using
      compactIdealDistance_le paperWoldHardyOperator 0 isCompactOperator_zero
  · exact le_compactIdealDistance _ 1 fun C hC =>
      paperWoldHardyOperator_sub_compact_norm_ge_one ⟨C, hC⟩

theorem paperWoldCriticalCompositeOperator_compactIdealDistance :
    compactIdealDistance paperWoldCriticalCompositeOperator = 1 := by
  rw [← paperWoldHardyOperator_distance, paperWoldHardyOperator_compactIdealDistance]

theorem paperWoldCriticalCompositeOperator_norm : ‖paperWoldCriticalCompositeOperator‖ = 1 := by
  apply le_antisymm paperWoldCriticalCompositeOperator_norm_le_one
  simpa only [sub_zero, paperWoldCriticalCompositeOperator_compactIdealDistance] using
    compactIdealDistance_le paperWoldCriticalCompositeOperator 0 isCompactOperator_zero

theorem paperWoldCompositeOperator_norm_le_one (t : {t : ℝ // t ≤ 1 / 2}) :
    ‖paperWoldCompositeOperator t‖ ≤ 1 := by
  simpa only [paperWoldCriticalCompositeOperator_norm] using paperWoldCompositeOperator_norm_le_critical t

theorem paperWoldCompositeOperator_scaled_norm_le_sharp (t : {t : ℝ // t ≤ 1 / 2}) :
    ‖paperWoldCompositeOperator t‖ ≤ (3 : ℝ) ^ (2 * (t : ℝ) - 1) := by
  rw [paperWoldCompositeOperator_factor]
  have h := (paperWoldCompositeDamping (paperWoldCompositeDampingTime t)).opNorm_comp_le
    paperWoldCriticalCompositeOperator
  rwa [paperWoldCriticalCompositeOperator_norm, mul_one, paperWoldCompositeDamping_norm,
    paperWoldCompositeDampingTime_coe, show -(1 - 2 * (t : ℝ)) = 2 * t - 1 by ring] at h

theorem paperWoldCompositeOperator_critical_difference_norm_le_one (t : {t : ℝ // t ≤ 1 / 2}) :
    ‖paperWoldCriticalCompositeOperator - paperWoldCompositeOperator t‖ ≤ 1 := by
  have he : paperWoldCriticalCompositeOperator - paperWoldCompositeOperator t =
      (paperWoldCompositeDamping 0 - paperWoldCompositeDamping (paperWoldCompositeDampingTime t)) ∘L
        paperWoldCriticalCompositeOperator := by
    rw [ContinuousLinearMap.sub_comp, paperWoldCompositeDamping_zero,
      ContinuousLinearMap.id_comp, paperWoldCompositeOperator_factor]
  rw [he]
  have h := (paperWoldCompositeDamping 0 - paperWoldCompositeDamping (paperWoldCompositeDampingTime t)).opNorm_comp_le
    paperWoldCriticalCompositeOperator
  rw [paperWoldCriticalCompositeOperator_norm, mul_one] at h
  exact h.trans (paperWoldCompositeDamping_sub_norm_le _ _)

theorem paperWoldCompositeOperator_critical_difference_compactIdealDistance
    (t : {t : ℝ // t < 1 / 2}) :
    compactIdealDistance (paperWoldCriticalCompositeOperator - paperWoldCompositeOperator ⟨t, t.property.le⟩) = 1 := by
  rw [paperWoldCompositeOperator_critical_compactIdealDistance,
    paperWoldCriticalCompositeOperator_compactIdealDistance]

/-- Every strict-half member is exactly one operator-norm unit from the native critical endpoint. -/
theorem paperWoldCompositeOperator_critical_difference_norm (t : {t : ℝ // t < 1 / 2}) :
    ‖paperWoldCriticalCompositeOperator - paperWoldCompositeOperator ⟨t, t.property.le⟩‖ = 1 := by
  apply le_antisymm (paperWoldCompositeOperator_critical_difference_norm_le_one _)
  simpa only [sub_zero, paperWoldCompositeOperator_critical_difference_compactIdealDistance] using
    compactIdealDistance_le
      (paperWoldCriticalCompositeOperator - paperWoldCompositeOperator ⟨t, t.property.le⟩) 0 isCompactOperator_zero

theorem paperWoldCompositeApproach_norm_tendsto_one :
    Tendsto (fun N => ‖paperWoldCompositeApproach N‖) atTop (𝓝 1) := by
  simpa only [paperWoldCriticalCompositeOperator_norm] using paperWoldCompositeApproach_norm_tendsto

theorem PaperHardy.Kernel.mask_norm_toOperator_le_one (K : PaperHardy.Kernel) (m : PaperWoldMask)
    (hK : ∀ n j, ‖K.entry n j‖ ≤ strictHalfHardyKernel n j) : ‖(K.mask m).toOperator‖ ≤ 1 := by
  apply PaperHardy.Kernel.norm_toOperator_le_one
  intro n j
  change ‖(m (n, j) : ℂ) * K.entry n j‖ ≤ _
  rw [norm_mul]
  exact ((mul_le_mul_of_nonneg_right (m (n, j)).property (norm_nonneg _)).trans_eq
    (one_mul _)).trans (hK n j)

theorem paperWoldHardyMaskedOperator_norm_le_one (m : PaperWoldMask) :
    ‖paperWoldHardyMaskedOperator m‖ ≤ 1 := by
  apply PaperHardy.Kernel.mask_norm_toOperator_le_one
  intro n j
  change ‖paperWoldHardyEntry n j‖ ≤ _
  rw [paperWoldHardyEntry_eq_strictHalfHardyKernel, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (strictHalfHardyKernel_nonneg n j)]

theorem paperWoldCriticalCompositeMaskedOperator_norm_le_one (m : PaperWoldMask) :
    ‖paperWoldCriticalCompositeMaskedOperator m‖ ≤ 1 :=
  PaperHardy.Kernel.mask_norm_toOperator_le_one _ _ paperWoldCompositeEntry_critical_sharp_bound

end
end RHTower
