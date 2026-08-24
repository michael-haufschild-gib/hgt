import GaloisForLFunctions.HTGeometry.ModelSpaceLeakageDenseRank
import GaloisForLFunctions.HTGeometry.FiniteBlaschkeGeneralizedSchurKernel
import GaloisForLFunctions.HTGeometry.HardyMultiplierZeroModelDimension

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Orthogonal model-space projection does not amplify the Hardy multiplier bound. -/
theorem norm_modelSpaceLeakageCore_le_bd (A B : DiskMultiplier) :
    ‖modelSpaceLeakageCore (hardyMultiplierModelSpace B) (hardyMul A)‖ ≤ A.bd := by
  let K := hardyMultiplierModelSpace B
  apply ContinuousLinearMap.opNorm_le_bound _ A.bd_nonneg
  intro x
  change ‖K.starProjection (hardyMul A x)‖ ≤ A.bd * ‖x‖
  calc
    ‖K.starProjection (hardyMul A x)‖ ≤
        ‖K.starProjection‖ * ‖hardyMul A x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖hardyMul A x‖ := by
      gcongr
      exact K.starProjection_norm_le
    _ = ‖hardyMul A x‖ := one_mul _
    _ ≤ ‖hardyMul A‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ A.bd * ‖x‖ :=
      mul_le_mul_of_nonneg_right (norm_hardyMul_le A) (norm_nonneg x)

/-- Evaluation at any denominator zero is a sharp pointwise lower bound for the norm of the
canonical projected Hardy leakage. -/
theorem norm_apply_le_norm_modelSpaceLeakageCore_of_zero
    (A B : DiskMultiplier) {a : ℂ} (ha : ‖a‖ < 1) (hB : B.fn a = 0) :
    ‖A.fn a‖ ≤
      ‖modelSpaceLeakageCore (hardyMultiplierModelSpace B) (hardyMul A)‖ := by
  let K := hardyMultiplierModelSpace B
  let v : K :=
    ⟨hardyKernel ha, hardyKernel_mem_hardyMultiplierModelSpace B ha hB⟩
  let T := modelSpaceLeakageCore K (hardyMul A)
  have hv : v ≠ 0 := by
    intro hzero
    apply hardyKernel_ne_zero ha
    exact congrArg Subtype.val hzero
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hadj : T.adjoint v =
      (starRingEnd ℂ) (A.fn a) • hardyKernel ha := by
    rw [adjoint_modelSpaceLeakageCore_apply,
      adjoint_hardyMul_hardyKernel]
  have hop := ContinuousLinearMap.le_opNorm T.adjoint v
  rw [hadj, norm_smul, RCLike.norm_conj,
    LinearIsometryEquiv.norm_map] at hop
  change ‖A.fn a‖ * ‖v‖ ≤ ‖T‖ * ‖v‖ at hop
  exact le_of_mul_le_mul_right hop hvpos

end

end GaloisForLFunctions.HTGeometry
