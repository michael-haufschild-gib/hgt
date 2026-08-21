import GaloisForLFunctions.HTGeometry.CartierDualBialgebra

/-!
# Cartier duality is an involution

For a commutative cocommutative `R`-bialgebra `A` that is finite and free as an `R`-module,
evaluation

`A → (A^∨)^∨,   a ↦ (f ↦ f a)`

is an isomorphism of bialgebras.  On group schemes this is the statement that the Cartier dual of
the Cartier dual of a finite flat commutative group scheme `N` is `N` itself, i.e. that the
canonical pairing `N × N^∨ → 𝔾_m` is perfect.

The three verifications are that evaluation carries the multiplication of `A` to the convolution
product of `A^∨∨`, the unit of `A` to the counit of `A^∨`, and the comultiplication of `A` to the
dual of the convolution product; each reduces to a computation on pure tensors through the
comparison map `T2c`.
-/

namespace GaloisForLFunctions.HTGeometry.CartierDualBialgebra

open Module TensorProduct Coalgebra
open GaloisForLFunctions.HTGeometry.DualCoalgebra
open GaloisForLFunctions.HTGeometry.CartierDual

variable (R A : Type*) [CommRing R] [CommRing A] [Bialgebra R A] [Coalgebra.IsCocomm R A]
  [Module.Free R A] [Module.Finite R A]

/-- Evaluation `A → (A^∨)^∨`. -/
noncomputable def doubleDualEquiv : A ≃ₗ[R] cartierDual R (cartierDual R A) :=
  (Module.evalEquiv R A) ≪≫ₗ (toDualEquiv R A).dualMap

variable {R A}

@[simp] theorem doubleDualEquiv_apply (a : A) (f : cartierDual R A) :
    toDual (doubleDualEquiv R A a) f = toDual f a := rfl

/-- Evaluating a decomposable functional on the tensor square of the Cartier dual through the
double dual is the comparison map `T2c`. -/
theorem mul'_map_doubleDual (a b : A) (u : cartierDual R A ⊗[R] cartierDual R A) :
    LinearMap.mul' R R
        (TensorProduct.map (toDual (doubleDualEquiv R A a)) (toDual (doubleDualEquiv R A b)) u)
      = T2c R A u (a ⊗ₜ[R] b) := by
  induction u with
  | zero => simp
  | add u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]
  | tmul f g =>
      rw [TensorProduct.map_tmul, LinearMap.mul'_apply, T2c_tmul_eq, T2_tmul,
        doubleDualEquiv_apply, doubleDualEquiv_apply]

/-- Evaluating a decomposable functional through the double dual on the image of the
comultiplication of `A`. -/
theorem T2c_map_doubleDual (f g : cartierDual R A) (w : A ⊗[R] A) :
    T2c R (cartierDual R A)
        (TensorProduct.map (doubleDualEquiv R A).toLinearMap (doubleDualEquiv R A).toLinearMap w)
        (f ⊗ₜ[R] g)
      = LinearMap.mul' R R (TensorProduct.map (toDual f) (toDual g) w) := by
  induction w with
  | zero => simp
  | add w w' hw hw' => simp only [map_add, LinearMap.add_apply, hw, hw']
  | tmul x y =>
      rw [TensorProduct.map_tmul, T2c_tmul_eq, T2_tmul, TensorProduct.map_tmul,
        LinearMap.mul'_apply]
      show toDual (doubleDualEquiv R A x) f * toDual (doubleDualEquiv R A y) g = _
      rw [doubleDualEquiv_apply, doubleDualEquiv_apply]

theorem doubleDualEquiv_one : doubleDualEquiv R A 1 = 1 := by
  refine (toDualEquiv R (cartierDual R A)).injective ?_
  refine LinearMap.ext fun f => ?_
  rw [show (toDualEquiv R (cartierDual R A)) (doubleDualEquiv R A 1)
      = toDual (doubleDualEquiv R A 1) from rfl,
    show (toDualEquiv R (cartierDual R A)) (1 : cartierDual R (cartierDual R A))
      = toDual (1 : cartierDual R (cartierDual R A)) from rfl,
    doubleDualEquiv_apply, one_def]
  rfl

theorem doubleDualEquiv_mul (a b : A) :
    doubleDualEquiv R A (a * b) = doubleDualEquiv R A a * doubleDualEquiv R A b := by
  refine (toDualEquiv R (cartierDual R A)).injective ?_
  refine LinearMap.ext fun f => ?_
  show toDual (doubleDualEquiv R A (a * b)) f
    = toDual (doubleDualEquiv R A a * doubleDualEquiv R A b) f
  rw [mul_def, doubleDualEquiv_apply]
  show _ = LinearMap.mul' R R (TensorProduct.map (toDual (doubleDualEquiv R A a))
    (toDual (doubleDualEquiv R A b)) (Coalgebra.comul f))
  rw [mul'_map_doubleDual, T2c_comul_tmul]

variable (R A)

/-- Evaluation `A → (A^∨)^∨` as an algebra isomorphism. -/
noncomputable def doubleDualAlgEquiv : A ≃ₐ[R] cartierDual R (cartierDual R A) :=
  AlgEquiv.ofLinearEquiv (doubleDualEquiv R A) doubleDualEquiv_one doubleDualEquiv_mul

variable {R A}

@[simp] theorem doubleDualAlgEquiv_apply (a : A) :
    doubleDualAlgEquiv R A a = doubleDualEquiv R A a := rfl

theorem doubleDualEquiv_counit (a : A) :
    (Coalgebra.counit (doubleDualEquiv R A a) : R) = Coalgebra.counit a := by
  rw [counit_def, doubleDualEquiv_apply, one_def]

theorem doubleDualEquiv_comul (a : A) :
    Coalgebra.comul (doubleDualEquiv R A a)
      = TensorProduct.map (doubleDualEquiv R A).toLinearMap (doubleDualEquiv R A).toLinearMap
          (Coalgebra.comul a) := by
  refine T2c_ext fun f g => ?_
  rw [T2c_comul_tmul, T2c_map_doubleDual, doubleDualEquiv_apply, mul_def]
  rfl

variable (R A)

/-- **Cartier duality is an involution**: evaluation `A → (A^∨)^∨` is an isomorphism of
bialgebras. -/
noncomputable def doubleDualBialgEquiv : A ≃ₐc[R] cartierDual R (cartierDual R A) :=
  BialgEquiv.ofAlgEquiv (doubleDualAlgEquiv R A)
    (by
      refine AlgHom.ext fun a => ?_
      show (Coalgebra.counit (doubleDualEquiv R A a) : R) = Coalgebra.counit a
      exact doubleDualEquiv_counit a)
    (by
      refine AlgHom.ext fun a => ?_
      show TensorProduct.map (doubleDualEquiv R A).toLinearMap
          (doubleDualEquiv R A).toLinearMap (Coalgebra.comul a)
        = Coalgebra.comul (doubleDualEquiv R A a)
      exact (doubleDualEquiv_comul a).symm)

end GaloisForLFunctions.HTGeometry.CartierDualBialgebra
