import GaloisForLFunctions.RHTower.PaperWoldHardyQuotient
import GaloisForLFunctions.HTGeometry.SharpHardySchur

/-! # Sharp norm budgets for the actual Hardy and composite operators -/

namespace RHTower
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- A stronger entrywise majorant improves the existing complete operator, preserving every row. -/
theorem PaperHardy.Kernel.norm_toOperator_le_one (K : PaperHardy.Kernel)
    (hK : ∀ n j, ‖K.entry n j‖ ≤ strictHalfHardyKernel n j) : ‖K.toOperator‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  have hs := strictHalfHardyKernel_energy_le (fun j => norm_nonneg (f j))
    (HilbertSchmidt.summable_coe_sq f)
  have hrow (n : ℕ) : ‖K.toOperator f n‖ ≤ ∑' j, strictHalfHardyKernel n j * ‖f j‖ := by
    rw [K.toOperator_apply]
    apply (norm_tsum_le_tsum_norm (K.row_summable f n).norm).trans
    exact Summable.tsum_le_tsum (fun j => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hK n j) (norm_nonneg _))
      (K.row_summable f n).norm
      (strictHalfHardyKernel_summable_row (fun j => norm_nonneg (f j))
        (HilbertSchmidt.summable_coe_sq f) n)
  have hsq : ‖K.toOperator f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [HilbertSchmidt.lp_norm_sq_eq, HilbertSchmidt.lp_norm_sq_eq]
    exact (Summable.tsum_le_tsum (fun n => pow_le_pow_left₀ (norm_nonneg _) (hrow n) 2)
      (HilbertSchmidt.summable_coe_sq _) hs.1).trans hs.2
  simpa only [one_mul] using (by nlinarith [norm_nonneg (K.toOperator f), norm_nonneg f] :
    ‖K.toOperator f‖ ≤ ‖f‖)

theorem paperWoldHardyEntry_eq_strictHalfHardyKernel (n j : ℕ) :
    paperWoldHardyEntry n j = (strictHalfHardyKernel n j : ℂ) := by
  unfold paperWoldHardyEntry strictHalfHardyKernel
  split_ifs <;> rfl

theorem paperWoldHardyOperator_norm_le_one : ‖paperWoldHardyOperator‖ ≤ 1 := by
  apply PaperHardy.Kernel.norm_toOperator_le_one
  intro n j
  change ‖paperWoldHardyEntry n j‖ ≤ _
  rw [paperWoldHardyEntry_eq_strictHalfHardyKernel, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (strictHalfHardyKernel_nonneg n j)]

theorem paperWoldCompositeEntry_critical_sharp_bound (n j : ℕ) :
    ‖paperWoldCompositeEntry (1 / 2) n j‖ ≤ strictHalfHardyKernel n j := by
  have h := paperWoldHardyDefect_re_nonneg (n, j)
  simp only [paperWoldHardyDefect, paperWoldHardyEntry_eq_strictHalfHardyKernel,
    Complex.sub_re, Complex.ofReal_re] at h
  rw [paperWoldCompositeEntry_norm_eq_re]
  linarith

theorem paperWoldCriticalCompositeOperator_norm_le_one : ‖paperWoldCriticalCompositeOperator‖ ≤ 1 :=
  PaperHardy.Kernel.norm_toOperator_le_one paperWoldCriticalCompositeKernel
    paperWoldCompositeEntry_critical_sharp_bound

end
end RHTower
