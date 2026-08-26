import GaloisForLFunctions.HTGeometry.AffineExponentialAntipodeComultiplication

/-!
# Antipode stability of iterated product-image kernels

An endomorphism of an affine source which realizes ambient inversion propagates factorwise to
all tensor powers.  Consequently every finite-product image kernel is stable under the ambient
antipode.  The final theorem specializes this reusable mechanism to `Gₐⁿ × Gₘⁿ`.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry

universe u

noncomputable section

/-- Tensor products of algebra homomorphisms preserve composition. -/
theorem tensorAlgHom_comp
    {k A₁ A₂ B₁ B₂ C₁ C₂ : Type u} [CommRing k]
    [CommRing A₁] [CommRing A₂] [CommRing B₁] [CommRing B₂]
    [CommRing C₁] [CommRing C₂]
    [Algebra k A₁] [Algebra k A₂] [Algebra k B₁] [Algebra k B₂]
    [Algebra k C₁] [Algebra k C₂]
    (f₁ : A₁ →ₐ[k] B₁) (g₁ : A₂ →ₐ[k] B₂)
    (f₂ : B₁ →ₐ[k] C₁) (g₂ : B₂ →ₐ[k] C₂) :
    (tensorAlgHom f₂ g₂).comp (tensorAlgHom f₁ g₁) =
      tensorAlgHom (f₂.comp f₁) (g₂.comp g₁) := by
  ext a <;> simp [tensorAlgHom]

/-- Apply one source endomorphism independently in every tensor factor. -/
def iteratedTensorAlgHom
    {k B : Type u} [CommRing k] [CommRing B] [Algebra k B]
    (σ : B →ₐ[k] B) : (m : ℕ) →
      IteratedTensorAlgebra k B m →ₐ[k] IteratedTensorAlgebra k B m
  | 0 => σ
  | Nat.succ m => tensorAlgHom σ (iteratedTensorAlgHom σ m)

@[simp] theorem iteratedTensorAlgHom_zero
    {k B : Type u} [CommRing k] [CommRing B] [Algebra k B]
    (σ : B →ₐ[k] B) : iteratedTensorAlgHom σ 0 = σ := rfl

@[simp] theorem iteratedTensorAlgHom_succ
    {k B : Type u} [CommRing k] [CommRing B] [Algebra k B]
    (σ : B →ₐ[k] B) (m : ℕ) :
    iteratedTensorAlgHom σ (m + 1) =
      tensorAlgHom σ (iteratedTensorAlgHom σ m) := rfl

/-- Source/ambient equivariance propagates to every nonempty finite product map. -/
theorem iteratedTensorAlgHom_comp_iteratedProductMap
    {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k B] [Bialgebra k A]
    (f : A →ₐ[k] B) (S : A →ₐ[k] A) (σ : B →ₐ[k] B)
    (hf : σ.comp f = f.comp S)
    (hS : (Bialgebra.comulAlgHom k A).comp S =
      (tensorAlgHom S S).comp (Bialgebra.comulAlgHom k A)) :
    ∀ m,
      (iteratedTensorAlgHom σ m).comp (iteratedProductMap f m) =
        (iteratedProductMap f m).comp S
  | 0 => hf
  | Nat.succ m => by
      rw [show iteratedProductMap f (Nat.succ m) =
        (tensorAlgHom f (iteratedProductMap f m)).comp
          (Bialgebra.comulAlgHom k A) by rfl]
      rw [show iteratedTensorAlgHom σ (Nat.succ m) =
        tensorAlgHom σ (iteratedTensorAlgHom σ m) by rfl]
      rw [← AlgHom.comp_assoc, tensorAlgHom_comp]
      rw [hf, iteratedTensorAlgHom_comp_iteratedProductMap f S σ hf hS m]
      rw [← tensorAlgHom_comp]
      exact (by
        simpa only [AlgHom.comp_assoc] using
          congrArg
            (fun q : A →ₐ[k] A ⊗[k] A =>
              (tensorAlgHom f (iteratedProductMap f m)).comp q)
            hS.symm)

/-- Every iterated product-image kernel is stable under an equivariant ambient endomorphism. -/
theorem iteratedProductKernel_endomorphism_mem
    {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k B] [Bialgebra k A]
    (f : A →ₐ[k] B) (S : A →ₐ[k] A) (σ : B →ₐ[k] B)
    (hf : σ.comp f = f.comp S)
    (hS : (Bialgebra.comulAlgHom k A).comp S =
      (tensorAlgHom S S).comp (Bialgebra.comulAlgHom k A))
    (m : ℕ) {a : A} (ha : a ∈ iteratedProductKernel f m) :
    S a ∈ iteratedProductKernel f m := by
  change iteratedProductMap f m (S a) = 0
  have h := DFunLike.congr_fun
    (iteratedTensorAlgHom_comp_iteratedProductMap f S σ hf hS m) a
  change iteratedTensorAlgHom σ m (iteratedProductMap f m a) =
    iteratedProductMap f m (S a) at h
  rw [← h]
  change iteratedTensorAlgHom σ m (iteratedProductMap f m a) = 0
  rw [show iteratedProductMap f m a = 0 by exact ha]
  exact map_zero _

/-- For affine-exponential coordinates, any source realization of inversion makes every finite
product-image kernel antipode-stable. -/
theorem affineExponential_iteratedProductKernel_antipode_mem
    (k B : Type u) [Field k] [CommRing B] [Algebra k B]
    {n : ℕ} (f : AffineExponentialGroup.CoordinateAlgebra k n →ₐ[k] B)
    (σ : B →ₐ[k] B)
    (hf : σ.comp f = f.comp
      (HopfAlgebra.antipodeAlgHom k
        (AffineExponentialGroup.CoordinateAlgebra k n)))
    (m : ℕ) {a : AffineExponentialGroup.CoordinateAlgebra k n}
    (ha : a ∈ iteratedProductKernel f m) :
    HopfAlgebra.antipode k a ∈ iteratedProductKernel f m := by
  exact iteratedProductKernel_endomorphism_mem f
    (HopfAlgebra.antipodeAlgHom k
      (AffineExponentialGroup.CoordinateAlgebra k n)) σ hf
    (affineExponential_comul_antipode k) m ha

end

end GaloisForLFunctions.HTGeometry
