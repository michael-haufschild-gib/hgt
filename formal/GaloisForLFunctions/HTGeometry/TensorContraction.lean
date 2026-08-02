import GaloisForLFunctions.HTGeometry.InjectiveTensorSeminorm
import GaloisForLFunctions.HTGeometry.SeminormNormingFunctional

/-!
# Contracting a tensor by a functional

A functional `φ` on the first factor contracts a tensor to the second factor, `x ⊗ y ↦ φ(x) • y`.
Pairing the contraction with a functional on the second factor is the dual pairing of the tensor,
so a seminorm of the contraction is bounded by the injective tensor seminorm — this is the estimate
that turns a trace-class expansion into a bound of the projective seminorm by the injective one.

* `tensorContract` : the contraction by a functional.
* `apply_tensorContract` : pairing the contraction is the dual pairing.
* `seminorm_tensorContract_le` : **`q(φ ⌟ z) ≤ ε(p, q)(z)`** when `‖φ‖ ≤ p`.
-/

open scoped TensorProduct

noncomputable section

namespace GaloisForLFunctions

variable {𝕜 X F : Type*} [RCLike 𝕜]
variable [AddCommGroup X] [Module 𝕜 X] [AddCommGroup F] [Module 𝕜 F]

/-- The contraction of a tensor by a functional on the first factor. -/
def tensorContract (φ : X →ₗ[𝕜] 𝕜) : X ⊗[𝕜] F →ₗ[𝕜] F :=
  TensorProduct.lift ((LinearMap.lsmul 𝕜 F).comp φ)

@[simp] theorem tensorContract_tmul (φ : X →ₗ[𝕜] 𝕜) (x : X) (y : F) :
    tensorContract φ (x ⊗ₜ[𝕜] y) = φ x • y := rfl

/-- Pairing a contraction with a functional on the second factor is the dual pairing. -/
theorem apply_tensorContract (φ : X →ₗ[𝕜] 𝕜) (ψ : F →ₗ[𝕜] 𝕜) (z : X ⊗[𝕜] F) :
    ψ (tensorContract φ z) = TensorProduct.lift (dualPairBilin φ ψ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [tensorContract_tmul, map_smul, TensorProduct.lift.tmul, dualPairBilin_apply,
      smul_eq_mul]
  | add z w hz hw =>
    rw [map_add, map_add, map_add, hz, hw]

/-- **A seminorm of a contraction is bounded by the injective tensor seminorm.** -/
theorem seminorm_tensorContract_le (p : Seminorm 𝕜 X) (q : Seminorm 𝕜 F) (φ : X →ₗ[𝕜] 𝕜)
    (hφ : ∀ x, ‖φ x‖ ≤ p x) (z : X ⊗[𝕜] F) :
    q (tensorContract φ z) ≤ injTensorSeminorm p q z := by
  obtain ⟨ψ, hψ, hval⟩ := exists_dual_le_seminorm_eq q (tensorContract φ z)
  rw [← hval, apply_tensorContract]
  exact norm_lift_le_injTensorSeminormFun p q hφ hψ z

/-- **A scaled bound for a contraction.** -/
theorem seminorm_tensorContract_le_mul (p : Seminorm 𝕜 X) (q : Seminorm 𝕜 F) (φ : X →ₗ[𝕜] 𝕜)
    {C : ℝ} (hC : 0 ≤ C) (hφ : ∀ x, ‖φ x‖ ≤ C * p x) (z : X ⊗[𝕜] F) :
    q (tensorContract φ z) ≤ C * injTensorSeminorm p q z := by
  rcases eq_or_lt_of_le hC with rfl | hCpos
  · have hzero : φ = 0 := by
      refine LinearMap.ext fun x => ?_
      have h := hφ x
      rw [zero_mul] at h
      rw [LinearMap.zero_apply]
      exact norm_le_zero_iff.mp h
    have hcz : tensorContract φ z = 0 := by
      rw [hzero]
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x f => simp
      | add a b ha hb =>
        rw [map_add, ha, hb, add_zero]
    rw [hcz, map_zero, zero_mul]
  · have hCne : ((C : 𝕜)) ≠ 0 := by
      refine RCLike.ofReal_ne_zero.mpr ?_
      exact hCpos.ne'
    have hnormC : ‖((C : 𝕜))‖ = C := by
      rw [RCLike.norm_ofReal, abs_of_pos hCpos]
    set φ' : X →ₗ[𝕜] 𝕜 := ((C : 𝕜))⁻¹ • φ with hφ'
    have hφ'bound : ∀ x, ‖φ' x‖ ≤ p x := by
      intro x
      rw [hφ', LinearMap.smul_apply, norm_smul, norm_inv, hnormC, inv_mul_le_iff₀ hCpos]
      exact hφ x
    have hscal : ∀ w : X ⊗[𝕜] F, tensorContract φ w = ((C : 𝕜)) • tensorContract φ' w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul x f =>
        rw [tensorContract_tmul, tensorContract_tmul, hφ', LinearMap.smul_apply, smul_eq_mul,
          smul_smul, ← mul_assoc, mul_inv_cancel₀ hCne, one_mul]
      | add a b ha hb =>
        rw [map_add, map_add, ha, hb, smul_add]
    rw [hscal z, map_smul_eq_mul q, hnormC]
    exact mul_le_mul_of_nonneg_left (seminorm_tensorContract_le p q φ' hφ'bound z) hCpos.le

end GaloisForLFunctions

end
