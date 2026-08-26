import GaloisForLFunctions.HTGeometry.IteratedBialgebraProductAntipode
import GaloisForLFunctions.HTGeometry.IteratedBialgebraProductCoideal

/-!
# Stable finite-product kernels are Hopf ideals

When a finite-product image kernel stabilizes, an identity-valued source point gives the counit
law, stable block multiplication gives the coideal law, and an equivariant source inversion gives
the antipode law.  These are exactly the three `IsHopfIdeal` obligations.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry

universe u

noncomputable section

/-- A stable product-image kernel with source identity and inversion is a Hopf ideal. -/
theorem iteratedProductKernel_isHopfIdeal
    {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k B] [HopfAlgebra k A]
    (f : A →ₐ[k] B) (e : B →ₐ[k] k)
    (he : e.comp f = Bialgebra.counitAlgHom k A)
    (σ : B →ₐ[k] B)
    (hσ : σ.comp f = f.comp (HopfAlgebra.antipodeAlgHom k A))
    (hS : (Bialgebra.comulAlgHom k A).comp
        (HopfAlgebra.antipodeAlgHom k A) =
      (tensorAlgHom
        (HopfAlgebra.antipodeAlgHom k A)
        (HopfAlgebra.antipodeAlgHom k A)).comp
          (Bialgebra.comulAlgHom k A))
    (m : ℕ)
    (hstable : iteratedProductKernel f (m + 1) = iteratedProductKernel f m) :
    (iteratedProductKernel f m).IsHopfIdeal k := by
  refine
    { counit_eq_zero := ?_
      map_mkQ_comul_eq_zero := ?_
      antipode_mem := ?_ }
  · intro a ha
    have ha0 : a ∈ iteratedProductKernel f 0 :=
      (iteratedProductKernel_antitone f e he (Nat.zero_le m)) ha
    have hfa : f a = 0 := ha0
    have h := DFunLike.congr_fun he a
    change e (f a) = Coalgebra.counit (R := k) a at h
    rw [hfa, map_zero] at h
    exact h.symm
  · intro a ha
    exact iteratedProductKernel_stable_comul_quotient_eq_zero f m hstable a ha
  · intro a ha
    exact iteratedProductKernel_endomorphism_mem f
      (HopfAlgebra.antipodeAlgHom k A) σ hσ hS m ha

/-- The stable-kernel Hopf package for the concrete affine-exponential coordinate algebra. -/
theorem affineExponential_iteratedProductKernel_isHopfIdeal
    (k B : Type u) [Field k] [CommRing B] [Algebra k B]
    {n : ℕ}
    (f : AffineExponentialGroup.CoordinateAlgebra k n →ₐ[k] B)
    (e : B →ₐ[k] k)
    (he : e.comp f = Bialgebra.counitAlgHom k
      (AffineExponentialGroup.CoordinateAlgebra k n))
    (σ : B →ₐ[k] B)
    (hσ : σ.comp f = f.comp
      (HopfAlgebra.antipodeAlgHom k
        (AffineExponentialGroup.CoordinateAlgebra k n)))
    (m : ℕ)
    (hstable : iteratedProductKernel f (m + 1) = iteratedProductKernel f m) :
    (iteratedProductKernel f m).IsHopfIdeal k := by
  exact iteratedProductKernel_isHopfIdeal f e he σ hσ
    (affineExponential_comul_antipode k) m hstable

end

end GaloisForLFunctions.HTGeometry
