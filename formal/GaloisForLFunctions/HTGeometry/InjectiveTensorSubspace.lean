import GaloisForLFunctions.HTGeometry.InjectiveTensorSeminorm
import Mathlib.Analysis.LocallyConvex.HahnBanach

/-!
# The injective tensor seminorm of a subspace

The injective tensor seminorm is computed by functionals, and a functional dominated by the
restriction of a seminorm to a subspace extends to the whole space with the same domination
(Hahn–Banach).  Hence the injective tensor seminorm of a tensor over a subspace is the same whether
it is computed in the subspace or in the ambient space: `ε` is a subspace-invariant seminorm.

This is the property the projective seminorm lacks, and the reason the injective seminorm is the
right comparison object for tensoring a strict injection.

* `lift_dualPairBilin_map` : the dual pairing commutes with `1 ⊗ j`.
* `injTensorSeminorm_map_le` : the injective seminorm decreases along bounded maps.
* `injTensorSeminorm_subtype_eq` : **the injective seminorm of a subspace is induced.**
-/

open scoped TensorProduct

noncomputable section

namespace GaloisForLFunctions

variable {𝕜 E A B : Type*} [NormedField 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [AddCommGroup A] [Module 𝕜 A]
variable [AddCommGroup B] [Module 𝕜 B]

/-! ## The dual pairing along a map -/

theorem lift_dualPairBilin_map (φ : E →ₗ[𝕜] 𝕜) (ψ : B →ₗ[𝕜] 𝕜) (j : A →ₗ[𝕜] B)
    (z : E ⊗[𝕜] A) :
    TensorProduct.lift (dualPairBilin φ (ψ.comp j)) z
      = TensorProduct.lift (dualPairBilin φ ψ) (TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) j z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    rw [TensorProduct.lift.tmul, TensorProduct.map_tmul, TensorProduct.lift.tmul,
      dualPairBilin_apply, dualPairBilin_apply, LinearMap.id_apply, LinearMap.comp_apply]
  | add z w hz hw =>
    rw [map_add, map_add, map_add, hz, hw]

/-! ## Monotonicity along bounded maps -/

/-- The injective seminorm decreases along a map that decreases the seminorms. -/
theorem injTensorSeminorm_map_le (p : Seminorm 𝕜 E) (qA : Seminorm 𝕜 A) (qB : Seminorm 𝕜 B)
    (j : A →ₗ[𝕜] B) (hj : ∀ a, qB (j a) ≤ qA a) (z : E ⊗[𝕜] A) :
    injTensorSeminorm p qB (TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) j z)
      ≤ injTensorSeminorm p qA z := by
  refine injTensorSeminormFun_le p qB _ ?_
  rintro r ⟨φ, ψ, hφ, hψ, rfl⟩
  have hcomp : ∀ a : A, ‖(ψ.comp j) a‖ ≤ qA a := by
    intro a
    exact le_trans (hψ (j a)) (hj a)
  have hval := lift_dualPairBilin_map φ ψ j z
  rw [← hval]
  exact norm_lift_le_injTensorSeminormFun p qA hφ hcomp z

/-- The dual pairing commutes with `j ⊗ 1`. -/
theorem lift_dualPairBilin_map_left {E' : Type*} [AddCommGroup E'] [Module 𝕜 E']
    (φ : E' →ₗ[𝕜] 𝕜) (ψ : A →ₗ[𝕜] 𝕜) (j : E →ₗ[𝕜] E') (z : E ⊗[𝕜] A) :
    TensorProduct.lift (dualPairBilin (φ.comp j) ψ) z
      = TensorProduct.lift (dualPairBilin φ ψ)
        (TensorProduct.map j (LinearMap.id : A →ₗ[𝕜] A) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    rw [TensorProduct.lift.tmul, TensorProduct.map_tmul, TensorProduct.lift.tmul,
      dualPairBilin_apply, dualPairBilin_apply, LinearMap.id_apply, LinearMap.comp_apply]
  | add z w hz hw =>
    rw [map_add, map_add, map_add, hz, hw]

/-- The injective seminorm decreases along a map of the first factor that decreases the
seminorms. -/
theorem injTensorSeminorm_map_left_le {E' : Type*} [AddCommGroup E'] [Module 𝕜 E']
    (p : Seminorm 𝕜 E) (p' : Seminorm 𝕜 E') (q : Seminorm 𝕜 A) (j : E →ₗ[𝕜] E')
    (hj : ∀ e, p' (j e) ≤ p e) (z : E ⊗[𝕜] A) :
    injTensorSeminorm p' q (TensorProduct.map j (LinearMap.id : A →ₗ[𝕜] A) z)
      ≤ injTensorSeminorm p q z := by
  refine injTensorSeminormFun_le p' q _ ?_
  rintro r ⟨φ, ψ, hφ, hψ, rfl⟩
  have hcomp : ∀ e : E, ‖(φ.comp j) e‖ ≤ p e := by
    intro e
    exact le_trans (hφ (j e)) (hj e)
  have hval := lift_dualPairBilin_map_left φ ψ j z
  rw [← hval]
  exact norm_lift_le_injTensorSeminormFun p q hcomp hψ z

/-! ## Subspaces -/

variable [IsRCLikeNormedField 𝕜]

/-- **The injective tensor seminorm of a subspace is induced from the ambient space.** -/
theorem injTensorSeminorm_subtype_eq (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 B) (S : Submodule 𝕜 B)
    (z : E ⊗[𝕜] S) :
    injTensorSeminorm p (q.comp S.subtype) z
      = injTensorSeminorm p q (TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) S.subtype z) := by
  refine le_antisymm ?_ ?_
  · refine injTensorSeminormFun_le p (q.comp S.subtype) z ?_
    rintro r ⟨φ, ψ, hφ, hψ, rfl⟩
    obtain ⟨g, hg, hgle⟩ :=
      Module.Dual.exists_extension_of_le_seminorm (𝕜 := 𝕜) (E := B) S ψ (p := q) hψ
    have hrestrict : g.comp S.subtype = ψ := by
      refine LinearMap.ext fun a => ?_
      rw [LinearMap.comp_apply, Submodule.subtype_apply]
      exact hg a
    have hval := lift_dualPairBilin_map φ g S.subtype z
    rw [hrestrict] at hval
    rw [hval]
    exact norm_lift_le_injTensorSeminormFun p q hφ hgle _
  · refine injTensorSeminorm_map_le p (q.comp S.subtype) q S.subtype ?_ z
    intro a
    rw [Seminorm.comp_apply]

end GaloisForLFunctions

end
