import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Freeness of an exterior algebra over the exterior algebra of a summand

The exterior algebra of a direct sum is the graded tensor product of the two exterior algebras,
because the exterior algebra is the Clifford algebra of the zero form and the zero form of a
product is the product of the zero forms.  Multiplication by an element of the first factor carries
no Koszul sign, so the underlying module is the ordinary tensor product with the first factor acting
on the left.  Hence the exterior algebra of a direct sum is a free module over the exterior algebra
of the first summand, on any basis of the exterior algebra of the second.

* `deningerExteriorProdEquiv` : the graded tensor product decomposition.
* `deningerExteriorProdEquiv_inl` : it carries the first exterior algebra to the left factor.
* `deningerExteriorProdTensorEquiv` : the induced module equivalence.
* `deningerExterior_free` : the freeness statement.
-/

namespace RHTower

open scoped TensorProduct

namespace DeningerExteriorProd

variable (k M₁ M₂ : Type*) [Field k] [AddCommGroup M₁] [Module k M₁]
  [AddCommGroup M₂] [Module k M₂]

/-- The graded tensor product of the exterior algebras of the two summands. -/
abbrev DeningerExtGradedTensor : Type _ :=
  CliffordAlgebra.evenOdd (0 : QuadraticForm k M₁) ᵍ⊗[k]
    CliffordAlgebra.evenOdd (0 : QuadraticForm k M₂)

/-- The zero quadratic form of a product is the product of the zero forms. -/
theorem deningerZeroQuadraticForm_prod :
    (0 : QuadraticForm k (M₁ × M₂))
      = (0 : QuadraticForm k M₁).prod (0 : QuadraticForm k M₂) := by
  ext x
  simp [QuadraticMap.prod]

/-- The identity is an isometry from the zero form to the product of the zero forms. -/
noncomputable def deningerZeroProdIsometry :
    (0 : QuadraticForm k (M₁ × M₂)).IsometryEquiv
      ((0 : QuadraticForm k M₁).prod (0 : QuadraticForm k M₂)) where
  toLinearEquiv := LinearEquiv.refl k (M₁ × M₂)
  map_app' m := by simp [QuadraticMap.prod]

/-- **The exterior algebra of a direct sum is the graded tensor product** of the exterior algebras
of the summands. -/
noncomputable def deningerExteriorProdEquiv :
    ExteriorAlgebra k (M₁ × M₂) ≃ₐ[k] DeningerExtGradedTensor k M₁ M₂ :=
  (CliffordAlgebra.equivOfIsometry (deningerZeroProdIsometry k M₁ M₂)).trans
    (CliffordAlgebra.prodEquiv _ _)

/-- The exterior algebra of the first summand includes into that of the sum. -/
noncomputable def deningerExtInl :
    ExteriorAlgebra k M₁ →ₐ[k] ExteriorAlgebra k (M₁ × M₂) :=
  ExteriorAlgebra.map (LinearMap.inl k M₁ M₂)

@[simp] theorem deningerExtInl_ι (m : M₁) :
    deningerExtInl k M₁ M₂ (ExteriorAlgebra.ι k m) = ExteriorAlgebra.ι k (m, 0) := by
  rw [deningerExtInl, ExteriorAlgebra.map_apply_ι]
  rfl

/-- **The decomposition carries the first exterior algebra to the left factor.** -/
theorem deningerExteriorProdEquiv_inl (a : ExteriorAlgebra k M₁) :
    deningerExteriorProdEquiv k M₁ M₂ (deningerExtInl k M₁ M₂ a)
      = GradedTensorProduct.includeLeft _ _ a := by
  have h : ((deningerExteriorProdEquiv k M₁ M₂).toAlgHom.comp (deningerExtInl k M₁ M₂))
      = GradedTensorProduct.includeLeft _ _ := by
    refine ExteriorAlgebra.hom_ext ?_
    refine LinearMap.ext fun m => ?_
    show deningerExteriorProdEquiv k M₁ M₂ (deningerExtInl k M₁ M₂ (ExteriorAlgebra.ι k m))
      = GradedTensorProduct.includeLeft _ _ (ExteriorAlgebra.ι k m)
    rw [deningerExtInl_ι, deningerExteriorProdEquiv]
    show (CliffordAlgebra.prodEquiv _ _)
        (CliffordAlgebra.equivOfIsometry (deningerZeroProdIsometry k M₁ M₂)
          (ExteriorAlgebra.ι k (m, 0))) = _
    rw [CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_apply_ι]
    show (CliffordAlgebra.prodEquiv _ _) (CliffordAlgebra.ι _ (m, 0)) = _
    simp [CliffordAlgebra.prodEquiv, CliffordAlgebra.ofProd_ι_mk]
  exact congrArg (fun F : ExteriorAlgebra k M₁ →ₐ[k] _ => F a) h

/-- Left multiplication in the graded tensor product by an element of the first factor carries no
Koszul sign. -/
theorem deningerGradedTmul_left (a x : ExteriorAlgebra k M₁) (y : ExteriorAlgebra k M₂) :
    ((a ᵍ⊗ₜ[k] (1 : ExteriorAlgebra k M₂) : DeningerExtGradedTensor k M₁ M₂)
        * (x ᵍ⊗ₜ[k] y)) = (a * x) ᵍ⊗ₜ[k] y := by
  have hsplit : (x ᵍ⊗ₜ[k] y : DeningerExtGradedTensor k M₁ M₂)
      = (x ᵍ⊗ₜ[k] (1 : ExteriorAlgebra k M₂)) * ((1 : ExteriorAlgebra k M₁) ᵍ⊗ₜ[k] y) :=
    (GradedTensorProduct.tmul_one_mul_one_tmul _ _ x y).symm
  have hmul : ((a ᵍ⊗ₜ[k] (1 : ExteriorAlgebra k M₂) : DeningerExtGradedTensor k M₁ M₂)
      * (x ᵍ⊗ₜ[k] (1 : ExteriorAlgebra k M₂)))
      = (a * x) ᵍ⊗ₜ[k] (1 : ExteriorAlgebra k M₂) := by
    have h := map_mul (GradedTensorProduct.includeLeftRingHom
      (CliffordAlgebra.evenOdd (0 : QuadraticForm k M₁))
      (CliffordAlgebra.evenOdd (0 : QuadraticForm k M₂))) a x
    simpa using h.symm
  rw [hsplit, ← mul_assoc, hmul, GradedTensorProduct.tmul_one_mul_one_tmul]

/-- The exterior algebra of the sum is a module over the exterior algebra of the first summand. -/
noncomputable scoped instance instModuleExtInl :
    Module (ExteriorAlgebra k M₁) (ExteriorAlgebra k (M₁ × M₂)) :=
  Module.compHom _ (deningerExtInl k M₁ M₂).toRingHom

theorem deningerExtInl_smul (a : ExteriorAlgebra k M₁) (z : ExteriorAlgebra k (M₁ × M₂)) :
    a • z = deningerExtInl k M₁ M₂ a * z := rfl

/-- The underlying module equivalence: the exterior algebra of the sum is the tensor product of the
exterior algebras of the summands. -/
noncomputable def deningerExtProdTensorLinearEquiv :
    (ExteriorAlgebra k M₁ ⊗[k] ExteriorAlgebra k M₂) ≃ₗ[k] ExteriorAlgebra k (M₁ × M₂) :=
  (GradedTensorProduct.of k _ _).trans (deningerExteriorProdEquiv k M₁ M₂).symm.toLinearEquiv

theorem deningerExtProdTensorLinearEquiv_tmul (x : ExteriorAlgebra k M₁)
    (y : ExteriorAlgebra k M₂) :
    deningerExtProdTensorLinearEquiv k M₁ M₂ (x ⊗ₜ[k] y)
      = (deningerExteriorProdEquiv k M₁ M₂).symm (x ᵍ⊗ₜ[k] y) := rfl

/-- **The tensor product is the exterior algebra of the sum, compatibly with the action of the
first factor.** -/
noncomputable def deningerExtProdTensorEquiv :
    (ExteriorAlgebra k M₁ ⊗[k] ExteriorAlgebra k M₂) ≃ₗ[ExteriorAlgebra k M₁]
      ExteriorAlgebra k (M₁ × M₂) where
  toFun := deningerExtProdTensorLinearEquiv k M₁ M₂
  map_add' := map_add _
  map_smul' a z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      have hsmul : a • (x ⊗ₜ[k] y : ExteriorAlgebra k M₁ ⊗[k] ExteriorAlgebra k M₂)
          = (a * x) ⊗ₜ[k] y := rfl
      rw [hsmul, deningerExtProdTensorLinearEquiv_tmul, RingHom.id_apply,
        deningerExtProdTensorLinearEquiv_tmul, deningerExtInl_smul,
        ← deningerGradedTmul_left, map_mul]
      congr 1
      show (deningerExteriorProdEquiv k M₁ M₂).symm
          (GradedTensorProduct.includeLeft _ _ a) = deningerExtInl k M₁ M₂ a
      rw [← deningerExteriorProdEquiv_inl, AlgEquiv.symm_apply_apply]
    | add u v hu hv =>
      rw [smul_add, map_add, map_add, hu, hv, ← smul_add]
  invFun := (deningerExtProdTensorLinearEquiv k M₁ M₂).symm
  left_inv := (deningerExtProdTensorLinearEquiv k M₁ M₂).left_inv
  right_inv := (deningerExtProdTensorLinearEquiv k M₁ M₂).right_inv

/-- **Freeness.**  The exterior algebra of a direct sum is a free module over the exterior algebra
of the first summand. -/
theorem deningerExterior_free :
    Module.Free (ExteriorAlgebra k M₁) (ExteriorAlgebra k (M₁ × M₂)) := by
  have hbasis : Module.Free (ExteriorAlgebra k M₁)
      (ExteriorAlgebra k M₁ ⊗[k] ExteriorAlgebra k M₂) :=
    Module.Free.of_basis (Algebra.TensorProduct.basis (ExteriorAlgebra k M₁)
      (Module.Free.chooseBasis k (ExteriorAlgebra k M₂)))
  exact Module.Free.of_equiv (deningerExtProdTensorEquiv k M₁ M₂)

end DeningerExteriorProd

namespace DeningerExteriorSub

open DeningerExteriorProd

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- The exterior algebra of the space is a module over the exterior algebra of a subspace. -/
noncomputable scoped instance instModuleExtSubtype (U : Submodule k V) :
    Module (ExteriorAlgebra k U) (ExteriorAlgebra k V) :=
  Module.compHom _ (ExteriorAlgebra.map U.subtype).toRingHom

theorem deningerExtSubtype_smul (U : Submodule k V) (a : ExteriorAlgebra k U)
    (z : ExteriorAlgebra k V) :
    a • z = ExteriorAlgebra.map U.subtype a * z := rfl

/-- A complementary pair identifies the space with the product of the two subspaces, isometrically
for the zero forms. -/
noncomputable def deningerComplIsometry {U W : Submodule k V} (h : IsCompl U W) :
    (0 : QuadraticForm k (U × W)).IsometryEquiv (0 : QuadraticForm k V) where
  toLinearEquiv := Submodule.prodEquivOfIsCompl U W h
  map_app' _ := rfl

/-- **Clause 1.**  For a subspace with a complement, the exterior algebra of the whole space is a
free module over the exterior algebra of the subspace. -/
theorem deningerExteriorSubmodule_free {U W : Submodule k V} (h : IsCompl U W) :
    Module.Free (ExteriorAlgebra k U) (ExteriorAlgebra k V) := by
  set E : ExteriorAlgebra k (U × W) ≃ₐ[k] ExteriorAlgebra k V :=
    CliffordAlgebra.equivOfIsometry (deningerComplIsometry h) with hE
  have hcomp : ∀ a : ExteriorAlgebra k U,
      E (deningerExtInl k U W a) = ExteriorAlgebra.map U.subtype a := by
    have hmaps : (E.toAlgHom.comp (deningerExtInl k U W))
        = ExteriorAlgebra.map (U.subtype) := by
      refine ExteriorAlgebra.hom_ext ?_
      refine LinearMap.ext fun u => ?_
      show E (deningerExtInl k U W (ExteriorAlgebra.ι k u))
        = ExteriorAlgebra.map U.subtype (ExteriorAlgebra.ι k u)
      rw [deningerExtInl_ι, ExteriorAlgebra.map_apply_ι, hE]
      show CliffordAlgebra.equivOfIsometry (deningerComplIsometry h)
          (ExteriorAlgebra.ι k ((u : U), (0 : W))) = _
      rw [CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_apply_ι]
      congr 1
      show (Submodule.prodEquivOfIsCompl U W h) ((u : U), (0 : W)) = (u : V)
      simp
    exact fun a => congrArg (fun F : ExteriorAlgebra k U →ₐ[k] _ => F a) hmaps
  have hlin : (ExteriorAlgebra k (U × W)) ≃ₗ[ExteriorAlgebra k U] (ExteriorAlgebra k V) :=
    { toFun := E
      map_add' := map_add _
      map_smul' := fun a z => by
        rw [deningerExtInl_smul, map_mul, RingHom.id_apply, deningerExtSubtype_smul, hcomp]
      invFun := E.symm
      left_inv := E.symm_apply_apply
      right_inv := E.apply_symm_apply }
  have hfree : Module.Free (ExteriorAlgebra k U) (ExteriorAlgebra k (U × W)) :=
    deningerExterior_free k U W
  exact Module.Free.of_equiv hlin

/-- **Clause 1.**  Over a field every subspace has a complement, so the exterior algebra of a
vector space is a free module over the exterior algebra of every subspace. -/
theorem deningerExteriorSubmodule_free_of_field (U : Submodule k V) :
    Module.Free (ExteriorAlgebra k U) (ExteriorAlgebra k V) := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl U
  exact deningerExteriorSubmodule_free hW

end DeningerExteriorSub

end RHTower
