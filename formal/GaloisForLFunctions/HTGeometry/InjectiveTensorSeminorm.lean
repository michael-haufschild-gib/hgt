import GaloisForLFunctions.HTGeometry.ProjectiveTensorSeminorm

/-!
# The injective tensor seminorm

For seminorms `p` on `E` and `q` on `F`, the injective tensor seminorm on `E ⊗[𝕜] F` is the
supremum of `|(φ ⊗ ψ)(z)|` over the functionals dominated by `p` and by `q`.  It is bounded by the
projective seminorm, and — unlike the projective one — it only involves functionals, so it is
computed the same way in a subspace as in the ambient space.

* `injTensorSeminorm` : **the injective tensor seminorm.**
* `injTensorSeminorm_le_projTensorSeminorm` : `ε ≤ π`.
* `injTensorSeminorm_tmul_le` : `ε(x ⊗ y) ≤ p(x) q(y)`.
-/

open scoped TensorProduct

noncomputable section

namespace GaloisForLFunctions

variable {𝕜 E F : Type*} [NormedField 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-! ## The bilinear form of a pair of functionals -/

/-- The bilinear form `(x, y) ↦ φ(x) ψ(y)`. -/
def dualPairBilin (φ : E →ₗ[𝕜] 𝕜) (ψ : F →ₗ[𝕜] 𝕜) : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜 where
  toFun x := φ x • ψ
  map_add' x y := by
    rw [map_add, add_smul]
  map_smul' c x := by
    rw [map_smul, smul_assoc]
    rfl

@[simp] theorem dualPairBilin_apply (φ : E →ₗ[𝕜] 𝕜) (ψ : F →ₗ[𝕜] 𝕜) (x : E) (y : F) :
    dualPairBilin φ ψ x y = φ x * ψ y := by
  show (φ x • ψ) y = φ x * ψ y
  rw [LinearMap.smul_apply, smul_eq_mul]

/-! ## The seminorm -/

/-- The values `|(φ ⊗ ψ)(z)|` over the functionals dominated by `p` and `q`. -/
def injTensorPairs (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (z : E ⊗[𝕜] F) : Set ℝ :=
  {r : ℝ | ∃ (φ : E →ₗ[𝕜] 𝕜) (ψ : F →ₗ[𝕜] 𝕜), (∀ x, ‖φ x‖ ≤ p x) ∧ (∀ y, ‖ψ y‖ ≤ q y) ∧
      r = ‖TensorProduct.lift (dualPairBilin φ ψ) z‖}

theorem lift_dualPairBilin_zero :
    TensorProduct.lift (dualPairBilin (0 : E →ₗ[𝕜] 𝕜) (0 : F →ₗ[𝕜] 𝕜)) = 0 := by
  refine TensorProduct.ext' fun x y => ?_
  rw [TensorProduct.lift.tmul, dualPairBilin_apply]
  simp

theorem injTensorPairs_nonempty (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (z : E ⊗[𝕜] F) :
    (injTensorPairs p q z).Nonempty := by
  refine ⟨0, 0, 0, fun x => ?_, fun y => ?_, ?_⟩
  · rw [LinearMap.zero_apply, norm_zero]
    exact apply_nonneg p x
  · rw [LinearMap.zero_apply, norm_zero]
    exact apply_nonneg q y
  · rw [lift_dualPairBilin_zero]
    simp

/-- Each dual pairing is bounded by the projective seminorm. -/
theorem norm_lift_dualPairBilin_le (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) {φ : E →ₗ[𝕜] 𝕜}
    {ψ : F →ₗ[𝕜] 𝕜} (hφ : ∀ x, ‖φ x‖ ≤ p x) (hψ : ∀ y, ‖ψ y‖ ≤ q y) (z : E ⊗[𝕜] F) :
    ‖TensorProduct.lift (dualPairBilin φ ψ) z‖ ≤ projTensorSeminorm p q z := by
  have hbound : ∀ (x : E) (y : F),
      normSeminorm 𝕜 𝕜 (dualPairBilin φ ψ x y) ≤ 1 * (p x * q y) := by
    intro x y
    show ‖dualPairBilin φ ψ x y‖ ≤ 1 * (p x * q y)
    rw [one_mul, dualPairBilin_apply, norm_mul]
    exact mul_le_mul (hφ x) (hψ y) (norm_nonneg _) (apply_nonneg p x)
  have h := projTensorSeminorm_lift_le p q (normSeminorm 𝕜 𝕜) (dualPairBilin φ ψ)
    zero_le_one hbound z
  rw [one_mul] at h
  exact h

theorem bddAbove_injTensorPairs (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (z : E ⊗[𝕜] F) :
    BddAbove (injTensorPairs p q z) := by
  refine ⟨projTensorSeminorm p q z, ?_⟩
  rintro r ⟨φ, ψ, hφ, hψ, rfl⟩
  exact norm_lift_dualPairBilin_le p q hφ hψ z

/-- The value of the injective tensor seminorm. -/
def injTensorSeminormFun (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (z : E ⊗[𝕜] F) : ℝ :=
  sSup (injTensorPairs p q z)

theorem injTensorSeminormFun_le (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (z : E ⊗[𝕜] F) {a : ℝ}
    (h : ∀ r ∈ injTensorPairs p q z, r ≤ a) : injTensorSeminormFun p q z ≤ a :=
  csSup_le (injTensorPairs_nonempty p q z) h

theorem le_injTensorSeminormFun (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) {z : E ⊗[𝕜] F} {r : ℝ}
    (h : r ∈ injTensorPairs p q z) : r ≤ injTensorSeminormFun p q z :=
  le_csSup (bddAbove_injTensorPairs p q z) h

theorem norm_lift_le_injTensorSeminormFun (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) {φ : E →ₗ[𝕜] 𝕜}
    {ψ : F →ₗ[𝕜] 𝕜} (hφ : ∀ x, ‖φ x‖ ≤ p x) (hψ : ∀ y, ‖ψ y‖ ≤ q y) (z : E ⊗[𝕜] F) :
    ‖TensorProduct.lift (dualPairBilin φ ψ) z‖ ≤ injTensorSeminormFun p q z :=
  le_injTensorSeminormFun p q ⟨φ, ψ, hφ, hψ, rfl⟩

theorem injTensorSeminormFun_nonneg (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (z : E ⊗[𝕜] F) :
    0 ≤ injTensorSeminormFun p q z := by
  refine le_injTensorSeminormFun p q ?_
  refine ⟨0, 0, fun x => ?_, fun y => ?_, ?_⟩
  · rw [LinearMap.zero_apply, norm_zero]
    exact apply_nonneg p x
  · rw [LinearMap.zero_apply, norm_zero]
    exact apply_nonneg q y
  · rw [lift_dualPairBilin_zero]
    simp

theorem injTensorSeminormFun_zero (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) :
    injTensorSeminormFun p q (0 : E ⊗[𝕜] F) = 0 := by
  refine le_antisymm ?_ (injTensorSeminormFun_nonneg p q 0)
  refine injTensorSeminormFun_le p q 0 ?_
  rintro r ⟨φ, ψ, _, _, rfl⟩
  rw [map_zero, norm_zero]

theorem injTensorSeminormFun_add_le (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (z w : E ⊗[𝕜] F) :
    injTensorSeminormFun p q (z + w)
      ≤ injTensorSeminormFun p q z + injTensorSeminormFun p q w := by
  refine injTensorSeminormFun_le p q (z + w) ?_
  rintro r ⟨φ, ψ, hφ, hψ, rfl⟩
  rw [map_add]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · exact norm_lift_le_injTensorSeminormFun p q hφ hψ z
  · exact norm_lift_le_injTensorSeminormFun p q hφ hψ w

theorem injTensorSeminormFun_smul_le (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (a : 𝕜)
    (z : E ⊗[𝕜] F) :
    injTensorSeminormFun p q (a • z) ≤ ‖a‖ * injTensorSeminormFun p q z := by
  refine injTensorSeminormFun_le p q (a • z) ?_
  rintro r ⟨φ, ψ, hφ, hψ, rfl⟩
  rw [map_smul, norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_lift_le_injTensorSeminormFun p q hφ hψ z)
    (norm_nonneg a)

theorem injTensorSeminormFun_smul (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (a : 𝕜)
    (z : E ⊗[𝕜] F) :
    injTensorSeminormFun p q (a • z) = ‖a‖ * injTensorSeminormFun p q z := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [injTensorSeminormFun_zero p q]
  · refine le_antisymm (injTensorSeminormFun_smul_le p q a z) ?_
    have h := injTensorSeminormFun_smul_le p q a⁻¹ (a • z)
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul, norm_inv] at h
    have h2 : ‖a‖ * injTensorSeminormFun p q z
        ≤ ‖a‖ * (‖a‖⁻¹ * injTensorSeminormFun p q (a • z)) :=
      mul_le_mul_of_nonneg_left h (norm_nonneg a)
    rw [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha), one_mul] at h2
    exact h2

/-- **The injective tensor seminorm.** -/
def injTensorSeminorm (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) : Seminorm 𝕜 (E ⊗[𝕜] F) where
  toFun := injTensorSeminormFun p q
  map_zero' := injTensorSeminormFun_zero p q
  add_le' := injTensorSeminormFun_add_le p q
  neg' z := by
    have h := injTensorSeminormFun_smul p q (-1 : 𝕜) z
    rw [neg_one_smul, norm_neg, norm_one, one_mul] at h
    exact h
  smul' := injTensorSeminormFun_smul p q

@[simp] theorem injTensorSeminorm_apply (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (z : E ⊗[𝕜] F) :
    injTensorSeminorm p q z = injTensorSeminormFun p q z := rfl

/-- **The injective seminorm is bounded by the projective seminorm.** -/
theorem injTensorSeminorm_le_projTensorSeminorm (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F)
    (z : E ⊗[𝕜] F) : injTensorSeminorm p q z ≤ projTensorSeminorm p q z := by
  refine injTensorSeminormFun_le p q z ?_
  rintro r ⟨φ, ψ, hφ, hψ, rfl⟩
  exact norm_lift_dualPairBilin_le p q hφ hψ z

/-- The injective seminorm is bounded by the product on pure tensors. -/
theorem injTensorSeminorm_tmul_le (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (x : E) (y : F) :
    injTensorSeminorm p q (x ⊗ₜ[𝕜] y) ≤ p x * q y :=
  le_trans (injTensorSeminorm_le_projTensorSeminorm p q (x ⊗ₜ[𝕜] y))
    (projTensorSeminorm_tmul_le p q x y)

end GaloisForLFunctions

end
