import GaloisForLFunctions.HTGeometry.SmirnovBoundaryQuotient
import GaloisForLFunctions.HTGeometry.HardyDiskModelSpace

open Complex Metric

namespace GaloisForLFunctions.HTGeometry

#check DenseRange
#check continuous_const.inner
#check continuous_id
#check isClosed_eq
#check inner_self_eq_zero
#check @div_le_div₀
#check @ContinuousLinearMap.integral_comp_comm
#check @Complex.reCLM.integral_comp_comm

theorem scratch_outer_ne_zero {phi : DiskMultiplier}
    (hphi : IsOuterDiskMultiplier phi) {a : ℂ} (ha : ‖a‖ < 1) :
    phi.fn a ≠ 0 := by
  intro hzero
  have hdense : DenseRange (hardyMul phi) :=
    (isOuterDiskMultiplier_iff_denseRange phi).mp hphi
  have hkill : ∀ f : HardyDisk,
      inner ℂ (hardyKernel ha) (hardyMul phi f) = 0 := by
    intro f
    rw [inner_hardyKernel ha, hardyFun_hardyMul phi f ha, hzero, zero_mul]
  have hclosed : IsClosed {f : HardyDisk | inner ℂ (hardyKernel ha) f = 0} := by
    exact isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hrange : Set.range (hardyMul phi) ⊆
      {f : HardyDisk | inner ℂ (hardyKernel ha) f = 0} := by
    rintro _ ⟨f, rfl⟩
    exact hkill f
  have hall : Set.univ ⊆ {f : HardyDisk | inner ℂ (hardyKernel ha) f = 0} := by
    rw [← hdense.closure_range]
    exact closure_minimal hrange hclosed
  have hself := hall (Set.mem_univ (hardyKernel ha))
  exact hardyKernel_ne_zero ha (inner_self_eq_zero.mp hself)

end GaloisForLFunctions.HTGeometry
