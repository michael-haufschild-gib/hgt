import GaloisForLFunctions.HTGeometry.AffineGroupSchemeCoLie
import GaloisForLFunctions.HTGeometry.DualCoalgebraFiniteFree
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# The Lie algebra of the Cartier dual

Let `A` be a commutative `R`-bialgebra which is finite and free as an `R`-module, so that
`N = Spec A` is a finite flat commutative group scheme and its Cartier dual `N^∨` is
`Spec (A^∨)` with `A^∨ = Hom_R(A, R)` under the convolution product

`(f ⋆ g)(a) = ⟨f ⊗ g, Δ a⟩`.

This file proves **Cartier duality on Lie algebras**:

`Lie (N^∨) = Prim A`,

i.e. `CartierDual.primitivesEquivCartierLie : primitives R A ≃ₗ[R] cartierPointDerivations R A`,
the isomorphism being evaluation `x ↦ (f ↦ f x)`.  A derivation at the identity of `Spec (A^∨)` is
a functional on `A^∨`, hence — `A` being finite free, so reflexive — evaluation at a unique
`x ∈ A`; the Leibniz rule for `⋆` says exactly that `Δ x = x ⊗ 1 + 1 ⊗ x`.

This is the object `Lie ℳ` for the Cartier-dual finite flat group scheme `ℳ` in Proposition 2.2(2)
of Suzuki, *Duality invariance of Faltings heights, Hodge line bundles and global periods*
(arXiv:2504.04993), and the reason the Lie algebras of `𝒩` and `ℳ` are dual to one another.
-/

namespace GaloisForLFunctions.HTGeometry.CartierDual

open Module TensorProduct Coalgebra
open GaloisForLFunctions.HTGeometry.AffineGroupScheme
open GaloisForLFunctions.HTGeometry.DualCoalgebra

variable (R A : Type*) [CommRing R] [CommRing A] [Bialgebra R A]
  [Module.Free R A] [Module.Finite R A]

/-- The **convolution product** on the dual of a coalgebra: `(f ⋆ g)(a) = ⟨f ⊗ g, Δ a⟩`.
This is the multiplication of the Cartier dual. -/
noncomputable def conv (f g : Dual R A) : Dual R A :=
  (LinearMap.mul' R R) ∘ₗ (TensorProduct.map f g) ∘ₗ (Coalgebra.comul : A →ₗ[R] A ⊗[R] A)

variable {R A}

theorem mul'_comp_map (f g : Dual R A) :
    (LinearMap.mul' R R) ∘ₗ (TensorProduct.map f g) = T2 R A (f ⊗ₜ[R] g) := by
  refine TensorProduct.ext' fun a b => ?_
  rw [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply, T2_tmul]

theorem conv_eq_T2 (f g : Dual R A) (a : A) :
    conv R A f g a = T2 R A (f ⊗ₜ[R] g) (comul a) := by
  rw [conv]
  show ((LinearMap.mul' R R) ∘ₗ (TensorProduct.map f g)) (comul a) = _
  rw [mul'_comp_map]

variable (R A)

/-- The `R`-module of derivations at the identity of the Cartier dual `Spec (A^∨)`. -/
def cartierPointDerivations : Submodule R (Dual R (Dual R A)) where
  carrier := {D | ∀ f g : Dual R A, D (conv R A f g) = f 1 * D g + g 1 * D f}
  add_mem' {D E} hD hE f g := by
    simp only [LinearMap.add_apply]
    rw [hD f g, hE f g]
    ring
  zero_mem' f g := by simp
  smul_mem' c D hD f g := by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    rw [hD f g]
    ring

variable {R A}

omit [Module.Free R A] [Module.Finite R A] in
theorem mem_cartierPointDerivations {D : Dual R (Dual R A)} :
    D ∈ cartierPointDerivations R A
      ↔ ∀ f g : Dual R A, D (conv R A f g) = f 1 * D g + g 1 * D f := Iff.rfl

/-- Two elements of `A ⊗ A` agree once all decomposable functionals agree on them. -/
theorem eq_of_T2_tmul_eq {y z : A ⊗[R] A}
    (h : ∀ f g : Dual R A, T2 R A (f ⊗ₜ[R] g) y = T2 R A (f ⊗ₜ[R] g) z) : y = z := by
  have h0 : ∀ u : Dual R A ⊗[R] Dual R A, T2 R A u y = T2 R A u z := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => exact h f g
    | add p q hp hq => rw [map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq]
  refine (Module.evalEquiv R (A ⊗[R] A)).injective ?_
  refine LinearMap.ext fun φ => ?_
  obtain ⟨u, rfl⟩ := (T2 R A).surjective φ
  exact h0 u

/-- **Cartier duality on Lie algebras.**  Evaluation at `x` is a derivation at the identity of the
Cartier dual exactly when `x` is primitive. -/
theorem evalEquiv_mem_cartierPointDerivations_iff (x : A) :
    (Module.evalEquiv R A x) ∈ cartierPointDerivations R A ↔ x ∈ primitives R A := by
  constructor
  · intro hD
    rw [mem_primitives]
    refine eq_of_T2_tmul_eq fun f g => ?_
    have h := hD f g
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply] at h
    rw [← conv_eq_T2]
    rw [h, map_add, T2_tmul, T2_tmul]
    ring
  · intro hx f g
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply]
    rw [conv_eq_T2, mem_primitives.mp hx, map_add, T2_tmul, T2_tmul]
    ring

theorem map_evalEquiv_primitives :
    Submodule.map (Module.evalEquiv R A).toLinearMap (primitives R A)
      = cartierPointDerivations R A := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (evalEquiv_mem_cartierPointDerivations_iff x).mpr hx
  · intro D hD
    obtain ⟨x, rfl⟩ := (Module.evalEquiv R A).surjective D
    exact ⟨x, (evalEquiv_mem_cartierPointDerivations_iff x).mp hD, rfl⟩

/-- **`Lie (N^∨) = Prim A`.** -/
noncomputable def primitivesEquivCartierLie :
    (primitives R A) ≃ₗ[R] (cartierPointDerivations R A) :=
  (Submodule.equivMapOfInjective (Module.evalEquiv R A).toLinearMap
      (Module.evalEquiv R A).injective (primitives R A)) ≪≫ₗ
    LinearEquiv.ofEq _ _ map_evalEquiv_primitives


/-! ### The Cartier dual is a bialgebra

The convolution product makes `A^∨` a commutative ring; the dual coalgebra structure of
`DualCoalgebraFiniteFree` makes it a coalgebra; and the two are compatible.  The compatibility is
exactly the statement that multiplication `A ⊗ A → A` of a bialgebra is a morphism of coalgebras
(mathlib's `Bialgebra.mulCoalgHom`), through the following functoriality of convolution. -/

/-- Convolution product on the dual of an arbitrary coalgebra. -/
noncomputable def convOf {C : Type*} [AddCommGroup C] [Module R C] [Coalgebra R C]
    (f g : Dual R C) : Dual R C :=
  (LinearMap.mul' R R) ∘ₗ (TensorProduct.map f g) ∘ₗ (Coalgebra.comul : C →ₗ[R] C ⊗[R] C)

omit [Module.Free R A] [Module.Finite R A] in
theorem conv_eq_convOf (f g : Dual R A) : conv R A f g = convOf f g := rfl

/-- **Functoriality of convolution**: pulling back along a coalgebra morphism is a ring map. -/
theorem convOf_comp_coalgHom {C D : Type*} [AddCommGroup C] [Module R C] [Coalgebra R C]
    [AddCommGroup D] [Module R D] [Coalgebra R D] (h : C →ₗc[R] D) (f g : Dual R D) :
    convOf (f ∘ₗ (h : C →ₗ[R] D)) (g ∘ₗ (h : C →ₗ[R] D))
      = (convOf f g) ∘ₗ (h : C →ₗ[R] D) := by
  refine LinearMap.ext fun c => ?_
  show (LinearMap.mul' R R) (TensorProduct.map (f ∘ₗ (h : C →ₗ[R] D)) (g ∘ₗ (h : C →ₗ[R] D))
      (Coalgebra.comul c))
    = (LinearMap.mul' R R) (TensorProduct.map f g (Coalgebra.comul (h c)))
  rw [TensorProduct.map_comp, LinearMap.comp_apply, ← CoalgHomClass.map_comp_comul_apply h]

theorem T2_dualComul_eq (f : Dual R A) :
    T2 R A (dualComul R A f) = f ∘ₗ (LinearMap.mul' R A) := by
  refine TensorProduct.ext' fun a b => ?_
  rw [T2_dualComul]
  rfl

/-- **The dual comultiplication is multiplicative**: `Δ'(f ⋆ g) = Δ' f ⋆ Δ' g`, the product on
the right being the convolution of the tensor-square coalgebra. -/
theorem T2_dualComul_conv (f g : Dual R A) :
    T2 R A (dualComul R A (conv R A f g))
      = convOf (T2 R A (dualComul R A f)) (T2 R A (dualComul R A g)) := by
  rw [T2_dualComul_eq, T2_dualComul_eq, T2_dualComul_eq, conv_eq_convOf]
  exact (convOf_comp_coalgHom (Bialgebra.mulCoalgHom R A) f g).symm

omit [Module.Free R A] [Module.Finite R A] in
/-- **The dual counit is multiplicative**: `ε'(f ⋆ g) = ε' f · ε' g`. -/
theorem dualCounit_conv (f g : Dual R A) :
    dualCounit R A (conv R A f g) = dualCounit R A f * dualCounit R A g := by
  show conv R A f g 1 = f 1 * g 1
  rw [conv, LinearMap.comp_apply, LinearMap.comp_apply, Bialgebra.comul_one]
  rfl

omit [Module.Free R A] [Module.Finite R A] in
/-- The unit of the convolution algebra on `A^∨` is the counit of `A`. -/
theorem convOf_counit_right (f : Dual R A) : convOf f (Coalgebra.counit : Dual R A) = f := by
  refine LinearMap.ext fun a => ?_
  show (LinearMap.mul' R R) (TensorProduct.map f (Coalgebra.counit : Dual R A)
    (Coalgebra.comul a)) = f a
  have hmap : TensorProduct.map f (Coalgebra.counit : A →ₗ[R] R)
      = (LinearMap.rTensor R f) ∘ₗ (LinearMap.lTensor A (Coalgebra.counit : A →ₗ[R] R)) := by
    refine TensorProduct.ext' fun x y => ?_
    simp
  rw [hmap, LinearMap.comp_apply, Coalgebra.lTensor_counit_comul, LinearMap.rTensor_tmul,
    LinearMap.mul'_apply, mul_one]

omit [Module.Free R A] [Module.Finite R A] in
theorem convOf_counit_left (f : Dual R A) : convOf (Coalgebra.counit : Dual R A) f = f := by
  refine LinearMap.ext fun a => ?_
  show (LinearMap.mul' R R) (TensorProduct.map (Coalgebra.counit : Dual R A) f
    (Coalgebra.comul a)) = f a
  have hmap : TensorProduct.map (Coalgebra.counit : A →ₗ[R] R) f
      = (LinearMap.lTensor R f) ∘ₗ (LinearMap.rTensor A (Coalgebra.counit : A →ₗ[R] R)) := by
    refine TensorProduct.ext' fun x y => ?_
    simp
  rw [hmap, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul, LinearMap.lTensor_tmul,
    LinearMap.mul'_apply, one_mul]

/-- `Δ'` sends the unit of `A^∨` to the unit of `A^∨ ⊗ A^∨`. -/
theorem T2_dualComul_counit :
    T2 R A (dualComul R A (Coalgebra.counit : Dual R A))
      = (Coalgebra.counit : Dual R (A ⊗[R] A)) := by
  refine TensorProduct.ext' fun a b => ?_
  rw [T2_dualComul]
  show (Coalgebra.counit : A →ₗ[R] R) (a * b)
    = (Coalgebra.counit : A →ₗ[R] R) b • (Coalgebra.counit : A →ₗ[R] R) a
  rw [Bialgebra.counit_mul, smul_eq_mul, mul_comm]

omit [Module.Free R A] [Module.Finite R A] in
/-- `ε'` sends the unit of `A^∨` to `1`. -/
@[simp] theorem dualCounit_counit :
    dualCounit R A (Coalgebra.counit : Dual R A) = 1 := Bialgebra.counit_one


/-! ### `T2` transports the tensor-square product to the convolution product

The last compatibility needed to see the Cartier dual as a bialgebra: the comparison
`T2 : A^∨ ⊗ A^∨ ≃ (A ⊗ A)^∨` carries the product of the tensor square of the convolution algebra
to the convolution product of the tensor-square coalgebra.  On pure tensors this is the identity

`(f ⋆ f')(a) · (g ⋆ g')(b) = ((f ⊗ g) ⋆ (f' ⊗ g'))(a ⊗ b)`,

which is exactly `Coalgebra.Repr.tmul`. -/

theorem convOf_apply_repr {C : Type*} [AddCommGroup C] [Module R C] [Coalgebra R C]
    (f g : Dual R C) (c : C) {κ : Type*} (rep : Coalgebra.Repr R c κ) :
    convOf f g c = ∑ i ∈ rep.index, f (rep.left i) * g (rep.right i) := by
  show (LinearMap.mul' R R) (TensorProduct.map f g (Coalgebra.comul c)) = _
  rw [← rep.eq, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.map_tmul, LinearMap.mul'_apply]

/-- **`T2` is multiplicative on pure tensors.** -/
theorem T2_tmul_convOf (f g f' g' : Dual R A) (a b : A) :
    T2 R A ((convOf f f') ⊗ₜ[R] (convOf g g')) (a ⊗ₜ[R] b)
      = convOf (T2 R A (f ⊗ₜ[R] g)) (T2 R A (f' ⊗ₜ[R] g')) (a ⊗ₜ[R] b) := by
  classical
  set Ra := Coalgebra.Repr.arbitrary R a with hRa
  set Rb := Coalgebra.Repr.arbitrary R b with hRb
  rw [T2_tmul, convOf_apply_repr f f' a Ra, convOf_apply_repr g g' b Rb,
    convOf_apply_repr _ _ (a ⊗ₜ[R] b) (Ra.tmul Rb)]
  simp only [Coalgebra.Repr.tmul_left, Coalgebra.Repr.tmul_right, Coalgebra.Repr.tmul_index,
    T2_tmul]
  rw [Finset.sum_product, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GaloisForLFunctions.HTGeometry.CartierDual
