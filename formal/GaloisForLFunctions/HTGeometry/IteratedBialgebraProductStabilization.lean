import GaloisForLFunctions.HTGeometry.IteratedBialgebraProductImage
import GaloisForLFunctions.HTGeometry.TensorProductLinearMapKernel

/-!
# Propagation of a stable affine product image

Once two consecutive finite product-image kernels agree, tensor exactness makes every later kernel
agree as well.
-/

open scoped TensorProduct
open Coalgebra Bialgebra

namespace GaloisForLFunctions.HTGeometry

universe u

/-- The algebra-hom tensor product has the expected underlying linear map. -/
theorem tensorAlgHom_toLinearMap
    {k A₁ A₂ B₁ B₂ : Type u} [Field k]
    [CommRing A₁] [CommRing A₂] [CommRing B₁] [CommRing B₂]
    [Algebra k A₁] [Algebra k A₂] [Algebra k B₁] [Algebra k B₂]
    (f : A₁ →ₐ[k] B₁) (g : A₂ →ₐ[k] B₂) :
    (tensorAlgHom f g).toLinearMap =
      TensorProduct.map f.toLinearMap g.toLinearMap := by
  ext a b
  simp

/-- Equality of two consecutive product-image kernels propagates to the next pair. -/
theorem iteratedProductKernel_eq_succ_propagates
    {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k B] [Bialgebra k A]
    (f : A →ₐ[k] B) (m : ℕ)
    (hstable : iteratedProductKernel f (m + 1) = iteratedProductKernel f m) :
    iteratedProductKernel f (m + 2) = iteratedProductKernel f (m + 1) := by
  have hker :
      LinearMap.ker (iteratedProductMap f (m + 1)).toLinearMap =
        LinearMap.ker (iteratedProductMap f m).toLinearMap := by
    ext a
    change (iteratedProductMap f (m + 1) a = 0) ↔
      (iteratedProductMap f m a = 0)
    change a ∈ iteratedProductKernel f (m + 1) ↔
      a ∈ iteratedProductKernel f m
    rw [hstable]
  have htensor := tensorProduct_map_ker_eq_of_right_ker_eq
    f.toLinearMap (iteratedProductMap f (m + 1)).toLinearMap
      (iteratedProductMap f m).toLinearMap hker
  ext a
  change tensorAlgHom f (iteratedProductMap f (m + 1))
      (Bialgebra.comulAlgHom k A a) = 0 ↔
    tensorAlgHom f (iteratedProductMap f m)
      (Bialgebra.comulAlgHom k A a) = 0
  have hleft := DFunLike.congr_fun
    (tensorAlgHom_toLinearMap f (iteratedProductMap f (m + 1)))
      (Bialgebra.comulAlgHom k A a)
  have hright := DFunLike.congr_fun
    (tensorAlgHom_toLinearMap f (iteratedProductMap f m))
      (Bialgebra.comulAlgHom k A a)
  change (tensorAlgHom f (iteratedProductMap f (m + 1))).toLinearMap
      (Bialgebra.comulAlgHom k A a) = 0 ↔
    (tensorAlgHom f (iteratedProductMap f m)).toLinearMap
      (Bialgebra.comulAlgHom k A a) = 0
  rw [hleft, hright]
  exact SetLike.ext_iff.mp htensor (Bialgebra.comulAlgHom k A a)

/-- After one consecutive equality, every later product-image kernel equals the stable kernel. -/
theorem iteratedProductKernel_stable_add
    {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k B] [Bialgebra k A]
    (f : A →ₐ[k] B) (m : ℕ)
    (hstable : iteratedProductKernel f (m + 1) = iteratedProductKernel f m) :
    ∀ r, iteratedProductKernel f (m + r) = iteratedProductKernel f m := by
  have hstep : ∀ r, iteratedProductKernel f (m + r + 1) =
      iteratedProductKernel f (m + r) := by
    intro r
    induction r with
    | zero => simpa using hstable
    | succ r ih =>
        simpa [Nat.add_assoc] using
          iteratedProductKernel_eq_succ_propagates f (m + r) ih
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.add_succ, hstep r, ih]

end GaloisForLFunctions.HTGeometry
