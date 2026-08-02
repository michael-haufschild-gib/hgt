import GaloisForLFunctions.RHTower.DeningerNuclearCompletedInvariance
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The projective tensor product of two seminorms

The projective seminorm of a tensor is the infimum, over all ways of writing it as a finite sum of
elementary tensors, of the sum of the products of the two seminorms.  Written with lists of pairs
so that two representations concatenate, the infimum is subadditive and homogeneous, hence a
seminorm.

It is the largest seminorm bounded by `p ⊗ q` on elementary tensors, and it is exactly what makes
a product of functionals continuous: a functional acting as `φ ⊗ ψ` on elementary tensors is
bounded by the product of the bounds of `φ` and `ψ`.

* `deningerTensorSeminorm` : the projective tensor product of two seminorms.
* `deningerTensorSeminorm_tmul_le` : the bound on elementary tensors.
* `deningerTensorSeminorm_dual_bound` : a product functional is bounded by the product of bounds.
-/

namespace RHTower

open scoped TensorProduct

section TensorSeminorm

variable {𝕜 E F : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F]

/-- The value of a representation of a tensor as a list of pairs. -/
def deningerTensorAux (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (L : List (E × F)) : ℝ :=
  (L.map fun z => p z.1 * q z.2).sum

theorem deningerTensorAux_nonneg (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (L : List (E × F)) :
    0 ≤ deningerTensorAux p q L := by
  refine List.sum_nonneg fun a ha => ?_
  obtain ⟨z, -, rfl⟩ := List.mem_map.mp ha
  exact mul_nonneg (apply_nonneg p _) (apply_nonneg q _)

theorem deningerTensorAux_append (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (L M : List (E × F)) :
    deningerTensorAux p q (L ++ M) = deningerTensorAux p q L + deningerTensorAux p q M := by
  simp [deningerTensorAux]

/-- The representations of a tensor as a finite sum of elementary tensors. -/
def deningerTensorLifts (u : E ⊗[𝕜] F) : Set (List (E × F)) :=
  {L | (L.map fun z => z.1 ⊗ₜ[𝕜] z.2).sum = u}

theorem deningerTensorLifts_zero : ([] : List (E × F)) ∈ deningerTensorLifts (0 : E ⊗[𝕜] F) := by
  simp [deningerTensorLifts]

theorem deningerTensorLifts_append {u v : E ⊗[𝕜] F} {L M : List (E × F)}
    (hL : L ∈ deningerTensorLifts u) (hM : M ∈ deningerTensorLifts v) :
    L ++ M ∈ deningerTensorLifts (u + v) := by
  show ((L ++ M).map fun z => z.1 ⊗ₜ[𝕜] z.2).sum = u + v
  rw [List.map_append, List.sum_append, hL, hM]

theorem deningerTensorLifts_nonempty (u : E ⊗[𝕜] F) : (deningerTensorLifts u).Nonempty := by
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨[], deningerTensorLifts_zero⟩
  | tmul x y => exact ⟨[(x, y)], by simp [deningerTensorLifts]⟩
  | add u v hu hv =>
      obtain ⟨L, hL⟩ := hu
      obtain ⟨M, hM⟩ := hv
      exact ⟨L ++ M, deningerTensorLifts_append hL hM⟩

/-- The norm of a list sum is at most the sum of the norms. -/
theorem deningerNorm_list_sum_le (l : List 𝕜) : ‖l.sum‖ ≤ (l.map fun x => ‖x‖).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.sum_cons, List.map_cons]
      exact (norm_add_le _ _).trans (by linarith)

theorem deningerTensorLifts_smul {u : E ⊗[𝕜] F} {L : List (E × F)}
    (hL : L ∈ deningerTensorLifts u) (a : 𝕜) :
    L.map (fun z => (a • z.1, z.2)) ∈ deningerTensorLifts (a • u) := by
  show ((L.map (fun z => (a • z.1, z.2))).map fun z => z.1 ⊗ₜ[𝕜] z.2).sum = a • u
  rw [List.map_map]
  have hfun : ((fun z : E × F => z.1 ⊗ₜ[𝕜] z.2) ∘ fun z : E × F => (a • z.1, z.2))
      = (fun w : E ⊗[𝕜] F => a • w) ∘ fun z : E × F => z.1 ⊗ₜ[𝕜] z.2 := by
    funext z
    simp [TensorProduct.smul_tmul']
  rw [hfun, ← List.map_map, ← List.smul_sum, hL]

theorem deningerTensorLifts_tmul (x : E) (y : F) :
    [(x, y)] ∈ deningerTensorLifts (x ⊗ₜ[𝕜] y) := by
  simp [deningerTensorLifts]

/-- The projective value of a tensor: the infimum of the values of its representations. -/
noncomputable def deningerTensorFun (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F)
    (u : E ⊗[𝕜] F) : ℝ :=
  ⨅ L : deningerTensorLifts u, deningerTensorAux p q L.1

theorem deningerTensorFun_bddBelow (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (u : E ⊗[𝕜] F) :
    BddBelow (Set.range fun L : deningerTensorLifts u => deningerTensorAux p q L.1) :=
  ⟨0, by
    rintro r ⟨L, rfl⟩
    exact deningerTensorAux_nonneg p q L.1⟩

theorem deningerTensorFun_nonneg (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (u : E ⊗[𝕜] F) :
    0 ≤ deningerTensorFun p q u := by
  haveI : Nonempty (deningerTensorLifts u) := (deningerTensorLifts_nonempty u).to_subtype
  exact le_ciInf fun L => deningerTensorAux_nonneg p q L.1

theorem deningerTensorFun_le_of_lift {p : Seminorm 𝕜 E} {q : Seminorm 𝕜 F} {u : E ⊗[𝕜] F}
    {L : List (E × F)} (hL : L ∈ deningerTensorLifts u) :
    deningerTensorFun p q u ≤ deningerTensorAux p q L :=
  ciInf_le (deningerTensorFun_bddBelow p q u) ⟨L, hL⟩

theorem deningerTensorFun_zero (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) :
    deningerTensorFun p q (0 : E ⊗[𝕜] F) = 0 :=
  le_antisymm
    (by simpa [deningerTensorAux] using
      deningerTensorFun_le_of_lift (p := p) (q := q) deningerTensorLifts_zero)
    (deningerTensorFun_nonneg p q 0)

theorem deningerTensorFun_add_le (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (u v : E ⊗[𝕜] F) :
    deningerTensorFun p q (u + v) ≤ deningerTensorFun p q u + deningerTensorFun p q v := by
  haveI : Nonempty (deningerTensorLifts u) := (deningerTensorLifts_nonempty u).to_subtype
  haveI : Nonempty (deningerTensorLifts v) := (deningerTensorLifts_nonempty v).to_subtype
  refine le_ciInf_add_ciInf fun L M => ?_
  refine le_trans (deningerTensorFun_le_of_lift (deningerTensorLifts_append L.2 M.2)) ?_
  exact le_of_eq (deningerTensorAux_append p q L.1 M.1)

theorem deningerTensorFun_smul_le (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (a : 𝕜)
    (u : E ⊗[𝕜] F) : deningerTensorFun p q (a • u) ≤ ‖a‖ * deningerTensorFun p q u := by
  haveI : Nonempty (deningerTensorLifts u) := (deningerTensorLifts_nonempty u).to_subtype
  simp only [deningerTensorFun]
  rw [Real.mul_iInf_of_nonneg (norm_nonneg a)]
  refine le_ciInf fun L => ?_
  refine le_trans (deningerTensorFun_le_of_lift (deningerTensorLifts_smul L.2 a)) ?_
  refine le_of_eq ?_
  simp only [deningerTensorAux, List.map_map, Function.comp_def, map_smul_eq_mul]
  rw [← List.sum_map_mul_left]
  simp [mul_assoc]

/-- **The projective tensor product of two seminorms.** -/
noncomputable def deningerTensorSeminorm (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) :
    Seminorm 𝕜 (E ⊗[𝕜] F) :=
  .ofSMulLE (deningerTensorFun p q) (deningerTensorFun_zero p q) (deningerTensorFun_add_le p q)
    (fun a u => deningerTensorFun_smul_le p q a u)

theorem deningerTensorSeminorm_apply (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (u : E ⊗[𝕜] F) :
    deningerTensorSeminorm p q u = deningerTensorFun p q u := rfl

/-- **The projective seminorm of an elementary tensor is at most the product.** -/
theorem deningerTensorSeminorm_tmul_le (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (x : E) (y : F) :
    deningerTensorSeminorm p q (x ⊗ₜ[𝕜] y) ≤ p x * q y := by
  refine le_trans (deningerTensorFun_le_of_lift (deningerTensorLifts_tmul x y)) ?_
  simp [deningerTensorAux]

/-- **A product of functionals is bounded by the product of the bounds.**  On any representation
the functional is the corresponding sum of products, so the estimate passes to the infimum. -/
theorem deningerTensorSeminorm_dual_bound {p : Seminorm 𝕜 E} {q : Seminorm 𝕜 F}
    {Φ : (E ⊗[𝕜] F) →ₗ[𝕜] 𝕜} {φ : E →ₗ[𝕜] 𝕜} {ψ : F →ₗ[𝕜] 𝕜}
    (hΦ : ∀ x y, Φ (x ⊗ₜ[𝕜] y) = φ x * ψ y) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hφ : ∀ x, ‖φ x‖ ≤ C * p x) (hψ : ∀ y, ‖ψ y‖ ≤ D * q y) (u : E ⊗[𝕜] F) :
    ‖Φ u‖ ≤ C * D * deningerTensorSeminorm p q u := by
  haveI : Nonempty (deningerTensorLifts u) := (deningerTensorLifts_nonempty u).to_subtype
  rw [deningerTensorSeminorm_apply, deningerTensorFun,
    Real.mul_iInf_of_nonneg (by positivity : (0 : ℝ) ≤ C * D)]
  refine le_ciInf fun L => ?_
  obtain ⟨M, hM⟩ := L
  have hval : Φ u = (M.map fun z => φ z.1 * ψ z.2).sum := by
    rw [← (hM : (M.map fun z => z.1 ⊗ₜ[𝕜] z.2).sum = u), map_list_sum, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun z _ => hΦ z.1 z.2)
  show ‖Φ u‖ ≤ C * D * deningerTensorAux p q M
  rw [hval]
  refine le_trans (deningerNorm_list_sum_le _) ?_
  rw [deningerTensorAux, ← List.sum_map_mul_left, List.map_map]
  refine List.sum_le_sum fun z _ => ?_
  show ‖φ z.1 * ψ z.2‖ ≤ C * D * (p z.1 * q z.2)
  calc ‖φ z.1 * ψ z.2‖ = ‖φ z.1‖ * ‖ψ z.2‖ := norm_mul _ _
    _ ≤ (C * p z.1) * (D * q z.2) :=
        mul_le_mul (hφ z.1) (hψ z.2) (norm_nonneg _) (by positivity)
    _ = C * D * (p z.1 * q z.2) := by ring

end TensorSeminorm

end RHTower
