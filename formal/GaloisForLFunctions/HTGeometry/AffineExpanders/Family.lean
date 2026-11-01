import GaloisForLFunctions.HTGeometry.AffineExpanders.Spectral

/-! # An explicit family of affine expanders

Eight affine maps on `(ℤ/(n+3)ℤ)²` give a uniform nonconstant spectral radius
at most `5√2/8 < 1`. The centering estimate applies to every function.
-/

namespace AffineExpanders

/-- A uniform spectral bound strictly below one for the MGG affine family. -/
theorem mgg_expander_family (n : ℕ) :
    spectralGap (mgg (n + 3)) ≤ 5 * Real.sqrt 2 / 8 ∧
      5 * Real.sqrt 2 / 8 < 1 := by
  refine ⟨spectralGap_mgg (n + 3) (by omega), ?_⟩
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith only [hs, Real.sqrt_nonneg 2]

/-- One affine random-walk step contracts the fluctuation about the mean. -/
theorem norm_mgg_centered_le (n : ℕ)
    (f : EuclideanSpace ℝ (Fin ((n + 3) * (n + 3)))) :
    ‖(mgg (n + 3)).walkCLM f - meanCLM ((n + 3) * (n + 3)) f‖ ≤
      (5 * Real.sqrt 2 / 8) * ‖f - meanCLM ((n + 3) * (n + 3)) f‖ := by
  have hWP := walkCLM_comp_meanCLM (mgg (n + 3)) (by omega) f
  have hPP : meanCLM ((n + 3) * (n + 3))
      (meanCLM ((n + 3) * (n + 3)) f) =
      meanCLM ((n + 3) * (n + 3)) f := by
    change (meanCLM _ * meanCLM _) f = _
    rw [meanCLM_idempotent]
  have heq : ((mgg (n + 3)).walkCLM - meanCLM ((n + 3) * (n + 3)))
      (f - meanCLM ((n + 3) * (n + 3)) f) =
      (mgg (n + 3)).walkCLM f - meanCLM ((n + 3) * (n + 3)) f := by
    simp only [_root_.sub_apply, map_sub, hWP, hPP, sub_self, sub_zero]
  rw [← heq]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (mgg_expander_family n).1 (norm_nonneg _))

end AffineExpanders
