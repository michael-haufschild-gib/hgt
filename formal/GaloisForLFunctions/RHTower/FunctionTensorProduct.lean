import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic

/-!
# Algebraic tensors of scalar-valued functions

The pointwise-product map from the algebraic tensor of two full function
spaces to functions on the product is injective over a field.  This is a
purely algebraic statement: no topology, measure, completion, or finite-
dimensionality premise is used.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open scoped TensorProduct

variable (K X Y : Type*) [Field K]

/-- Pointwise product as a bilinear map on full scalar-valued function
spaces. -/
def functionTensorProductBilinear :
    (X → K) →ₗ[K] (Y → K) →ₗ[K] (X × Y → K) :=
  LinearMap.mk₂ K (fun f g z => f z.1 * g z.2)
    (fun f f' g => by ext z; simp [add_mul])
    (fun c f g => by ext z; simp [mul_assoc])
    (fun f g g' => by ext z; simp [mul_add])
    (fun c f g => by ext z; simp [mul_left_comm])

/-- Pointwise-product map from the algebraic tensor of full function
spaces. -/
def functionTensorProductHom :
    (X → K) ⊗[K] (Y → K) →ₗ[K] (X × Y → K) :=
  TensorProduct.lift (functionTensorProductBilinear K X Y)

@[simp]
theorem functionTensorProductHom_tmul
    (f : X → K) (g : Y → K) (z : X × Y) :
    functionTensorProductHom K X Y (f ⊗ₜ[K] g) z =
      f z.1 * g z.2 :=
  rfl

/-- Finite sums of separated scalar-valued functions have unique algebraic
tensor coefficients. -/
theorem functionTensorProductHom_injective :
    Function.Injective (functionTensorProductHom K X Y) := by
  classical
  let b := Module.Basis.ofVectorSpace K (Y → K)
  intro t u htu
  let e := TensorProduct.equivFinsuppOfBasisRight (M := X → K) b
  apply e.injective
  ext i x
  let c := e t - e u
  have hfun :
      functionTensorProductHom K X Y (t - u) = 0 := by
    rw [map_sub, htu, sub_self]
  have hrepr :
      t - u = c.sum (fun i f => f ⊗ₜ[K] b i) := by
    calc
      t - u = e.symm (e (t - u)) :=
        (e.symm_apply_apply (t - u)).symm
      _ = e.symm c := by simp [c]
      _ = c.sum (fun i f => f ⊗ₜ[K] b i) :=
        TensorProduct.equivFinsuppOfBasisRight_symm_apply b c
  have hlin :
      c.sum (fun i f => f x • b i) = 0 := by
    ext y
    have hy := congrFun hfun (x, y)
    rw [hrepr] at hy
    simpa [Finsupp.sum, functionTensorProductHom,
      functionTensorProductBilinear, map_sum,
      LinearMap.sum_apply] using hy
  let d : Module.Basis.ofVectorSpaceIndex K (Y → K) →₀ K :=
    c.mapRange (fun f => f x) (by simp)
  have hd : d = 0 := by
    apply b.repr.symm.injective
    rw [map_zero, b.repr_symm_apply,
      Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index]
    · exact hlin
    · simp
  have hci : c i x = 0 := by
    have hi := congrArg
      (fun z : Module.Basis.ofVectorSpaceIndex K (Y → K) →₀ K =>
        z i) hd
    simpa [d] using hi
  change (e t) i x = (e u) i x
  simpa [c, sub_eq_zero] using hci

end

end GaloisForLFunctions.RHTower
