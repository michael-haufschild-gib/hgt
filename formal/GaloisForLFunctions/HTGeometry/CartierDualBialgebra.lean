import GaloisForLFunctions.HTGeometry.CartierDualLieAlgebra
import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# The Cartier dual as a bialgebra

For a commutative `R`-bialgebra `A` that is finite and free as an `R`-module, `N = Spec A` is a
finite flat commutative group scheme and its Cartier dual is `N^∨ = Spec (A^∨)`, where
`A^∨ = Hom_R(A, R)` carries

* the **convolution product** `(f ⋆ g)(a) = ⟨f ⊗ g, Δ a⟩`, with unit the counit of `A`;
* the **dual comultiplication** `⟨Δ' f, a ⊗ b⟩ = f(a b)`, with counit `f ↦ f 1`.

This file bundles the two into a single `Bialgebra R (cartierDual R A)` instance on a type synonym
for `Module.Dual R A`.  The ring structure is transported from mathlib's convolution ring on
`WithConv (A →ₗ[R] R)`; the coalgebra structure is the one built in `DualCoalgebraFiniteFree`; the
compatibility is `T2_dualComul_conv` together with the multiplicativity of the comparison map
`T2 : A^∨ ⊗ A^∨ ≃ (A ⊗ A)^∨`.
-/

namespace GaloisForLFunctions.HTGeometry

open Module TensorProduct Coalgebra
open GaloisForLFunctions.HTGeometry.DualCoalgebra
open GaloisForLFunctions.HTGeometry.CartierDual

variable (R A : Type*) [CommRing R] [CommRing A] [Bialgebra R A] [Coalgebra.IsCocomm R A]
  [Module.Free R A] [Module.Finite R A]

/-- The **Cartier dual** `A^∨` of a finite free commutative `R`-bialgebra `A`, as a type synonym
of the linear dual carrying the convolution product. -/
def cartierDual : Type _ := Module.Dual R A

namespace CartierDualBialgebra

instance : AddCommGroup (cartierDual R A) := inferInstanceAs (AddCommGroup (Module.Dual R A))

instance : Module R (cartierDual R A) := inferInstanceAs (Module R (Module.Dual R A))

variable {R A}

/-- The underlying functional of an element of the Cartier dual. -/
def toDual (f : cartierDual R A) : Module.Dual R A := f

/-- An element of the Cartier dual attached to a functional. -/
def ofDual (f : Module.Dual R A) : cartierDual R A := f

omit [Coalgebra.IsCocomm R A] [Module.Free R A] [Module.Finite R A] in
@[simp] theorem toDual_ofDual (f : Module.Dual R A) : toDual (ofDual f) = f := rfl

omit [Coalgebra.IsCocomm R A] [Module.Free R A] [Module.Finite R A] in
@[simp] theorem ofDual_toDual (f : cartierDual R A) : ofDual (toDual f) = f := rfl

/-! ### Bilinearity and associativity of the convolution product -/

section Conv

variable {C : Type*} [AddCommGroup C] [Module R C] [Coalgebra R C]

theorem convOf_add_left (f f' g : Module.Dual R C) :
    convOf (R := R) (f + f') g = convOf f g + convOf f' g := by
  show (LinearMap.mul' R R) ∘ₗ (TensorProduct.map (f + f') g) ∘ₗ
      (Coalgebra.comul : C →ₗ[R] C ⊗[R] C) = _
  rw [TensorProduct.map_add_left, LinearMap.add_comp, LinearMap.comp_add]
  rfl

theorem convOf_add_right (f g g' : Module.Dual R C) :
    convOf (R := R) f (g + g') = convOf f g + convOf f g' := by
  show (LinearMap.mul' R R) ∘ₗ (TensorProduct.map f (g + g')) ∘ₗ
      (Coalgebra.comul : C →ₗ[R] C ⊗[R] C) = _
  rw [TensorProduct.map_add_right, LinearMap.add_comp, LinearMap.comp_add]
  rfl

theorem convOf_smul_left (r : R) (f g : Module.Dual R C) :
    convOf (R := R) (r • f) g = r • convOf f g := by
  show (LinearMap.mul' R R) ∘ₗ (TensorProduct.map (r • f) g) ∘ₗ
      (Coalgebra.comul : C →ₗ[R] C ⊗[R] C) = _
  rw [TensorProduct.map_smul_left, LinearMap.smul_comp, LinearMap.comp_smul]
  rfl

theorem convOf_smul_right (r : R) (f g : Module.Dual R C) :
    convOf (R := R) f (r • g) = r • convOf f g := by
  show (LinearMap.mul' R R) ∘ₗ (TensorProduct.map f (r • g)) ∘ₗ
      (Coalgebra.comul : C →ₗ[R] C ⊗[R] C) = _
  rw [TensorProduct.map_smul_right, LinearMap.smul_comp, LinearMap.comp_smul]
  rfl

theorem convOf_zero_left (g : Module.Dual R C) : convOf (R := R) 0 g = 0 := by
  have h := convOf_add_left (R := R) (0 : Module.Dual R C) 0 g
  rw [add_zero] at h
  have h2 : convOf (R := R) (0 : Module.Dual R C) g + 0
      = convOf (R := R) (0 : Module.Dual R C) g + convOf (R := R) (0 : Module.Dual R C) g := by
    rw [add_zero]
    exact h
  exact (add_left_cancel h2).symm

theorem convOf_zero_right (f : Module.Dual R C) : convOf (R := R) f 0 = 0 := by
  have h := convOf_add_right (R := R) f 0 0
  rw [add_zero] at h
  have h2 : convOf (R := R) f (0 : Module.Dual R C) + 0
      = convOf (R := R) f (0 : Module.Dual R C) + convOf (R := R) f (0 : Module.Dual R C) := by
    rw [add_zero]
    exact h
  exact (add_left_cancel h2).symm

/-- Associativity of the convolution product, transported from mathlib's convolution ring on
`WithConv (C →ₗ[R] R)`. -/
theorem convOf_comm [Coalgebra.IsCocomm R C] (f g : Module.Dual R C) :
    convOf (R := R) f g = convOf g f :=
  congrArg (@WithConv.ofConv (Module.Dual R C))
    (mul_comm (WithConv.toConv f) (WithConv.toConv g))

theorem convOf_assoc (f g h : Module.Dual R C) :
    convOf (R := R) (convOf f g) h = convOf f (convOf g h) :=
  congrArg (@WithConv.ofConv (Module.Dual R C))
    (mul_assoc (WithConv.toConv f) (WithConv.toConv g) (WithConv.toConv h))

end Conv

variable (R A)

noncomputable instance instCommRing : CommRing (cartierDual R A) :=
  { (inferInstance : AddCommGroup (cartierDual R A)) with
    mul_comm := fun f g => congrArg ofDual (convOf_comm (toDual f) (toDual g))
    mul := fun f g => ofDual (convOf (R := R) (toDual f) (toDual g))
    one := ofDual (Coalgebra.counit : Module.Dual R A)
    mul_assoc := fun f g h => congrArg ofDual (convOf_assoc (toDual f) (toDual g) (toDual h))
    one_mul := fun f => congrArg ofDual (convOf_counit_left (toDual f))
    mul_one := fun f => congrArg ofDual (convOf_counit_right (toDual f))
    left_distrib := fun f g h =>
      congrArg ofDual (convOf_add_right (toDual f) (toDual g) (toDual h))
    right_distrib := fun f g h =>
      congrArg ofDual (convOf_add_left (toDual f) (toDual g) (toDual h))
    zero_mul := fun f => congrArg ofDual (convOf_zero_left (toDual f))
    mul_zero := fun f => congrArg ofDual (convOf_zero_right (toDual f)) }

noncomputable instance instAlgebra : Algebra R (cartierDual R A) :=
  Algebra.ofModule
    (fun r x y => congrArg ofDual (convOf_smul_left r (toDual x) (toDual y)))
    (fun r x y => congrArg ofDual (convOf_smul_right r (toDual x) (toDual y)))

variable {R A}

omit [Module.Free R A] [Module.Finite R A] in
/-- The product of the Cartier dual is the convolution product. -/
theorem mul_def (f g : cartierDual R A) :
    toDual (f * g) = convOf (R := R) (toDual f) (toDual g) := rfl

omit [Module.Free R A] [Module.Finite R A] in
/-- The unit of the Cartier dual is the counit of `A`. -/
theorem one_def : toDual (1 : cartierDual R A) = (Coalgebra.counit : Module.Dual R A) := rfl

variable (R A)

noncomputable instance instCoalgebra : Coalgebra R (cartierDual R A) := dualCoalgebra R A

variable {R A}

@[simp] theorem comul_def (f : cartierDual R A) :
    (Coalgebra.comul f : cartierDual R A ⊗[R] cartierDual R A) = dualComul R A (toDual f) := rfl

@[simp] theorem counit_def (f : cartierDual R A) :
    (Coalgebra.counit f : R) = toDual f 1 := rfl

/-! ### The comparison map on the tensor square -/

variable (R A)

/-- The Cartier dual and the linear dual are the same `R`-module. -/
def toDualEquiv : cartierDual R A ≃ₗ[R] Module.Dual R A where
  toFun := toDual
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := ofDual
  left_inv _ := rfl
  right_inv _ := rfl

/-- The comparison `A^∨ ⊗ A^∨ ≃ (A ⊗ A)^∨` for the Cartier dual. -/
noncomputable def T2c :
    cartierDual R A ⊗[R] cartierDual R A ≃ₗ[R] Module.Dual R (A ⊗[R] A) :=
  (TensorProduct.congr (toDualEquiv R A) (toDualEquiv R A)) ≪≫ₗ T2 R A

variable {R A}

omit [Module.Free R A] [Module.Finite R A] in
theorem congr_toDualEquiv (u : cartierDual R A ⊗[R] cartierDual R A) :
    TensorProduct.congr (toDualEquiv R A) (toDualEquiv R A) u = u := by
  induction u with
  | zero => exact map_zero _
  | tmul f g => rfl
  | add u v hu hv =>
      rw [map_add, hu, hv]
      exact rfl

theorem T2c_apply (u : cartierDual R A ⊗[R] cartierDual R A) :
    T2c R A u = T2 R A u := by
  show T2 R A ((TensorProduct.congr (toDualEquiv R A) (toDualEquiv R A)) u) = _
  rw [congr_toDualEquiv]

theorem T2c_tmul_eq (f g : cartierDual R A) :
    T2c R A (f ⊗ₜ[R] g) = T2 R A ((toDual f) ⊗ₜ[R] (toDual g)) := by
  show T2 R A ((TensorProduct.congr (toDualEquiv R A) (toDualEquiv R A)) (f ⊗ₜ[R] g)) = _
  rw [TensorProduct.congr_tmul]
  rfl

/-! ### `T2` is multiplicative -/

omit [Coalgebra.IsCocomm R A] in
/-- The comparison `T2` carries the tensor-square product to the convolution product, on pure
tensors. -/
theorem T2_tmul_mul (f g f' g' : Module.Dual R A) :
    T2 R A ((convOf (R := R) f f') ⊗ₜ[R] (convOf (R := R) g g'))
      = convOf (R := R) (T2 R A (f ⊗ₜ[R] g)) (T2 R A (f' ⊗ₜ[R] g')) := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => exact T2_tmul_convOf f g f' g' a b
  | add p q hp hq => rw [map_add, map_add, hp, hq]

/-- **The comparison `T2` is multiplicative.** -/
theorem T2c_mul (u v : cartierDual R A ⊗[R] cartierDual R A) :
    T2c R A (u * v) = convOf (R := R) (T2c R A u) (T2c R A v) := by
  induction u with
  | zero => rw [zero_mul, map_zero, convOf_zero_left]
  | add u u' hu hu' => rw [add_mul, map_add, hu, hu', map_add, convOf_add_left]
  | tmul f f' =>
      induction v with
      | zero => rw [mul_zero, map_zero, convOf_zero_right]
      | add v v' hv hv' => rw [mul_add, map_add, hv, hv', map_add, convOf_add_right]
      | tmul g g' =>
          rw [Algebra.TensorProduct.tmul_mul_tmul, T2c_tmul_eq, T2c_tmul_eq, T2c_tmul_eq,
            mul_def, mul_def]
          exact T2_tmul_mul (toDual f) (toDual f') (toDual g) (toDual g')

/-! ### The bialgebra structure -/

theorem cartier_counit_one : (Coalgebra.counit (1 : cartierDual R A) : R) = 1 := by
  rw [counit_def, one_def]
  exact Bialgebra.counit_one

theorem cartier_counit_mul (f g : cartierDual R A) :
    (Coalgebra.counit (f * g) : R) = Coalgebra.counit f * Coalgebra.counit g := by
  rw [counit_def, counit_def, counit_def, mul_def]
  exact dualCounit_conv (toDual f) (toDual g)

omit [Coalgebra.IsCocomm R A] in
theorem T2_counit_tmul :
    T2 R A ((Coalgebra.counit : Module.Dual R A) ⊗ₜ[R] (Coalgebra.counit : Module.Dual R A))
      = (Coalgebra.counit : Module.Dual R (A ⊗[R] A)) := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      rw [T2_tmul]
      show (Coalgebra.counit : Module.Dual R A) a * (Coalgebra.counit : Module.Dual R A) b
        = (Coalgebra.counit : Module.Dual R A) b • (Coalgebra.counit : Module.Dual R A) a
      rw [smul_eq_mul, mul_comm]
  | add p q hp hq => rw [map_add, map_add, hp, hq]

theorem T2c_comul (f : cartierDual R A) :
    T2c R A (Coalgebra.comul f) = T2 R A (dualComul R A (toDual f)) := by
  rw [T2c_apply, comul_def]

theorem cartier_comul_one :
    (Coalgebra.comul (1 : cartierDual R A) : cartierDual R A ⊗[R] cartierDual R A) = 1 := by
  refine (T2c R A).injective ?_
  rw [T2c_comul, one_def, T2_dualComul_counit, Algebra.TensorProduct.one_def, T2c_tmul_eq,
    one_def, T2_counit_tmul]

theorem cartier_comul_mul (f g : cartierDual R A) :
    (Coalgebra.comul (f * g) : cartierDual R A ⊗[R] cartierDual R A)
      = Coalgebra.comul f * Coalgebra.comul g := by
  refine (T2c R A).injective ?_
  rw [T2c_comul, mul_def, T2c_mul, T2c_comul, T2c_comul]
  exact T2_dualComul_conv (toDual f) (toDual g)

/-- **The Cartier dual of a finite free commutative bialgebra is a bialgebra.** -/
noncomputable instance instBialgebra : Bialgebra R (cartierDual R A) :=
  Bialgebra.mk' R (cartierDual R A) cartier_counit_one (fun {_ _} => cartier_counit_mul _ _)
    cartier_comul_one (fun {_ _} => cartier_comul_mul _ _)

/-! ### The Cartier dual is again finite free and cocommutative -/

instance instFree : Module.Free R (cartierDual R A) :=
  inferInstanceAs (Module.Free R (Module.Dual R A))

instance instFinite : Module.Finite R (cartierDual R A) :=
  inferInstanceAs (Module.Finite R (Module.Dual R A))

/-- Two elements of the tensor square of the Cartier dual agree as soon as the corresponding
functionals on `A ⊗ A` agree on pure tensors. -/
theorem T2c_ext {u v : cartierDual R A ⊗[R] cartierDual R A}
    (h : ∀ a b : A, T2c R A u (a ⊗ₜ[R] b) = T2c R A v (a ⊗ₜ[R] b)) : u = v := by
  refine (T2c R A).injective (LinearMap.ext fun x => ?_)
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => exact h a b
  | add p q hp hq => rw [map_add, map_add, hp, hq]

theorem T2c_comm (u : cartierDual R A ⊗[R] cartierDual R A) (a b : A) :
    T2c R A (TensorProduct.comm R (cartierDual R A) (cartierDual R A) u) (a ⊗ₜ[R] b)
      = T2c R A u (b ⊗ₜ[R] a) := by
  induction u with
  | zero => simp
  | add u v hu hv => rw [map_add, map_add, LinearMap.add_apply, hu, hv, map_add,
      LinearMap.add_apply]
  | tmul f g =>
      rw [TensorProduct.comm_tmul, T2c_tmul_eq, T2c_tmul_eq, T2_tmul, T2_tmul, mul_comm]

theorem T2c_comul_tmul (f : cartierDual R A) (a b : A) :
    T2c R A (Coalgebra.comul f) (a ⊗ₜ[R] b) = toDual f (a * b) := by
  rw [T2c_comul, T2_dualComul]

/-- **The Cartier dual of a commutative bialgebra is cocommutative.** -/
instance instIsCocomm : Coalgebra.IsCocomm R (cartierDual R A) where
  comm_comp_comul := by
    refine LinearMap.ext fun f => ?_
    refine T2c_ext fun a b => ?_
    show T2c R A (TensorProduct.comm R (cartierDual R A) (cartierDual R A)
        (Coalgebra.comul f)) (a ⊗ₜ[R] b) = _
    rw [T2c_comm, T2c_comul_tmul, T2c_comul_tmul, mul_comm]

end CartierDualBialgebra

end GaloisForLFunctions.HTGeometry
