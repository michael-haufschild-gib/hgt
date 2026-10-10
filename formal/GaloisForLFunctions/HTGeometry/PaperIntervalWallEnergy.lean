import GaloisForLFunctions.HTGeometry.PaperIntervalWallFourier

/-! # Exact spectral energy retained by the two chambers

Every assignment at the midpoint has the same unit square-integral and the same unit
Parseval mass. Fourier completion retains the chamber energy while erasing the wall value.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory Filter
open scoped Topology

theorem paperIntervalWallStep_energy (w : ℂ) : l2NormSq (paperIntervalWallStep w) = 1 := by
  unfold l2NormSq
  calc
    _ = ∫ _ in (0 : ℝ)..1, (1 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne (1 / 2 : ℝ)] with x hx
      intro _
      rcases lt_or_gt_of_ne hx with h | h
      · simp only [paperIntervalWallStep, if_pos h, norm_neg, norm_one, one_pow]
      · simp only [paperIntervalWallStep, if_neg (not_lt.mpr h.le), if_pos h,
          norm_one, one_pow]
    _ = 1 := by norm_num

/-- The complete Fourier spectrum retains exactly one unit of chamber energy. -/
theorem paperIntervalWallStep_parseval (w : ℂ) :
    HasSum (fun k : ℤ => ‖l2Pair (fourierChar k) (paperIntervalWallStep w)‖ ^ 2) 1 := by
  have h := hasSum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
    (paperIntervalWallStep_memLp w)
  have he := paperIntervalWallStep_energy w
  unfold l2NormSq at he
  simpa only [fourierCoeffOn_eq_l2Pair, sub_zero, inv_one, one_smul,
    he] using h

end
end GaloisForLFunctions.HTGeometry
