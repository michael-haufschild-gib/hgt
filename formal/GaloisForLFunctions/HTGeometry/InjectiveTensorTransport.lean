import GaloisForLFunctions.HTGeometry.InjectiveTensorSubspace

/-!
# Transporting the injective tensor seminorm

Two further properties of the injective tensor seminorm, both proved from the dual description:

* it is monotone in the second seminorm, with constants — a domination `q₁ ≤ C q₂` transports to
  `ε(p,q₁) ≤ C ε(p,q₂)`;
* it is invariant under an injective map of the second factor carrying the seminorms to each other,
  because a functional dominated by the pulled-back seminorm extends along the injection
  (Hahn–Banach on the range).

Together they carry a strict injection through a tensor product: the injective seminorm of a tensor
over the source equals the one over the target, up to the strictness constants.

* `injTensorSeminorm_le_mul_of_le` : **scaled monotonicity.**
* `injTensorSeminorm_injective_eq` : **invariance along an injective map.**
-/

open scoped TensorProduct

noncomputable section

namespace GaloisForLFunctions

variable {𝕜 E A B : Type*} [RCLike 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [AddCommGroup A] [Module 𝕜 A]
variable [AddCommGroup B] [Module 𝕜 B]

/-! ## Scaling the second functional -/

theorem lift_dualPairBilin_smul_right (φ : E →ₗ[𝕜] 𝕜) (ψ : A →ₗ[𝕜] 𝕜) (c : 𝕜)
    (z : E ⊗[𝕜] A) :
    TensorProduct.lift (dualPairBilin φ (c • ψ)) z
      = c * TensorProduct.lift (dualPairBilin φ ψ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    rw [TensorProduct.lift.tmul, TensorProduct.lift.tmul, dualPairBilin_apply,
      dualPairBilin_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  | add z w hz hw =>
    rw [map_add, map_add, hz, hw, mul_add]

/-- **Scaled monotonicity of the injective tensor seminorm in the second seminorm.** -/
theorem injTensorSeminorm_le_mul_of_le (p : Seminorm 𝕜 E) (q₁ q₂ : Seminorm 𝕜 A) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ a, q₁ a ≤ C * q₂ a) (z : E ⊗[𝕜] A) :
    injTensorSeminorm p q₁ z ≤ C * injTensorSeminorm p q₂ z := by
  refine injTensorSeminormFun_le p q₁ z ?_
  rintro r ⟨φ, ψ, hφ, hψ, rfl⟩
  rcases eq_or_lt_of_le hC with rfl | hCpos
  · have hzero : ψ = 0 := by
      refine LinearMap.ext fun a => ?_
      have h1 := hψ a
      have h2 := h a
      rw [zero_mul] at h2
      rw [LinearMap.zero_apply]
      exact norm_le_zero_iff.mp (le_trans h1 h2)
    have hval : TensorProduct.lift (dualPairBilin φ ψ) z = 0 := by
      rw [hzero]
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x a => simp
      | add u v hu hv => rw [map_add, hu, hv, add_zero]
    rw [hval, norm_zero, zero_mul]
  · have hCne : ((C : 𝕜)) ≠ 0 := RCLike.ofReal_ne_zero.mpr hCpos.ne'
    have hnormC : ‖((C : 𝕜))‖ = C := by
      rw [RCLike.norm_ofReal, abs_of_pos hCpos]
    have hψ' : ∀ a, ‖(((C : 𝕜))⁻¹ • ψ) a‖ ≤ q₂ a := by
      intro a
      rw [LinearMap.smul_apply, norm_smul, norm_inv, hnormC, inv_mul_le_iff₀ hCpos]
      exact le_trans (hψ a) (h a)
    have hsmul : TensorProduct.lift (dualPairBilin φ ψ) z
        = ((C : 𝕜)) * TensorProduct.lift (dualPairBilin φ (((C : 𝕜))⁻¹ • ψ)) z := by
      rw [lift_dualPairBilin_smul_right, ← mul_assoc, mul_inv_cancel₀ hCne, one_mul]
    rw [hsmul, norm_mul, hnormC]
    exact mul_le_mul_of_nonneg_left
      (norm_lift_le_injTensorSeminormFun p q₂ hφ hψ' z) hCpos.le

/-! ## Invariance along an injective map -/

/-- **The injective tensor seminorm is invariant along an injective map** of the second factor
carrying the seminorms to each other. -/
theorem injTensorSeminorm_injective_eq (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 B) (j : A →ₗ[𝕜] B)
    (hinj : Function.Injective j) (z : E ⊗[𝕜] A) :
    injTensorSeminorm p (q.comp j) z
      = injTensorSeminorm p q (TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) j z) := by
  refine le_antisymm ?_ ?_
  · refine injTensorSeminormFun_le p (q.comp j) z ?_
    rintro r ⟨φ, ψ, hφ, hψ, rfl⟩
    set e := LinearEquiv.ofInjective j hinj with he
    set ψ₀ : Module.Dual 𝕜 (LinearMap.range j) := ψ.comp (e.symm : (LinearMap.range j) →ₗ[𝕜] A)
      with hψ₀
    have hdom : ∀ v : (LinearMap.range j), ‖ψ₀ v‖ ≤ q (v : B) := by
      intro v
      have hv : j (e.symm v) = (v : B) := by
        have := e.apply_symm_apply v
        exact congrArg Subtype.val this
      have hval : ψ₀ v = ψ (e.symm v) := rfl
      rw [hval]
      refine le_trans (hψ (e.symm v)) (le_of_eq ?_)
      rw [Seminorm.comp_apply, hv]
    obtain ⟨ψ', hψ'eq, hψ'le⟩ :=
      Module.Dual.exists_extension_of_le_seminorm (LinearMap.range j) ψ₀ hdom
    have hcomp : ψ'.comp j = ψ := by
      refine LinearMap.ext fun a => ?_
      have hmem : j a ∈ LinearMap.range j := ⟨a, rfl⟩
      have h1 : ψ' (j a) = ψ₀ ⟨j a, hmem⟩ := hψ'eq ⟨j a, hmem⟩
      have h2 : ψ₀ ⟨j a, hmem⟩ = ψ (e.symm ⟨j a, hmem⟩) := rfl
      have h3 : e.symm ⟨j a, hmem⟩ = a := by
        refine hinj ?_
        have := e.apply_symm_apply ⟨j a, hmem⟩
        exact congrArg Subtype.val this
      rw [LinearMap.comp_apply, h1, h2, h3]
    have hval := lift_dualPairBilin_map φ ψ' j z
    rw [hcomp] at hval
    rw [hval]
    exact norm_lift_le_injTensorSeminormFun p q hφ hψ'le _
  · refine injTensorSeminorm_map_le p (q.comp j) q j ?_ z
    intro a
    rw [Seminorm.comp_apply]

end GaloisForLFunctions

end
