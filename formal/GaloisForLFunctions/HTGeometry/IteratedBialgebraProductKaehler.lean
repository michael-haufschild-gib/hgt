import GaloisForLFunctions.HTGeometry.IteratedBialgebraProductImage
import GaloisForLFunctions.HTGeometry.KaehlerAlgHomGenericVanishing

/-!
# Invariant Kähler vanishing on iterated product sources

If an invariant Kähler differential vanishes on one affine source, its multiplication pullback law
forces it to vanish on every nonempty finite product of that source.  This is the differential
counterpart of the iterated product-image construction.
-/

open scoped TensorProduct
open Coalgebra Bialgebra

namespace GaloisForLFunctions.HTGeometry

universe u

noncomputable section

/-- Vanishing of an invariant differential propagates through every iterated product map. -/
theorem algHomKaehlerMap_iteratedProductMap_eq_zero
    {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k B] [Bialgebra k A]
    (f : A →ₐ[k] B) (w : Ω[A⁄k])
    (hcomul :
      algHomKaehlerMap (Bialgebra.comulAlgHom k A) w =
        algHomKaehlerMap
            (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A) w +
          algHomKaehlerMap
            (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A) w)
    (hf : algHomKaehlerMap f w = 0) :
    ∀ m, algHomKaehlerMap (iteratedProductMap f m) w = 0 := by
  intro m
  induction m with
  | zero => exact hf
  | succ m ih =>
      let g : A →ₐ[k] IteratedTensorAlgebra k B m := iteratedProductMap f m
      let Φ : A ⊗[k] A →ₐ[k] B ⊗[k] IteratedTensorAlgebra k B m := tensorAlgHom f g
      have hleftHom : Φ.comp
            (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A) =
          (Algebra.TensorProduct.includeLeft : B →ₐ[k]
            B ⊗[k] IteratedTensorAlgebra k B m).comp f := by
        apply DFunLike.ext _ _
        intro a
        simp [Φ, tensorAlgHom]
      have hrightHom : Φ.comp
            (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A) =
          (Algebra.TensorProduct.includeRight : IteratedTensorAlgebra k B m →ₐ[k]
            B ⊗[k] IteratedTensorAlgebra k B m).comp g := by
        apply DFunLike.ext _ _
        intro a
        simp [Φ, tensorAlgHom]
      have hleft : algHomKaehlerMap Φ
          (algHomKaehlerMap
            (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A) w) = 0 := by
        rw [← algHomKaehlerMap_comp, hleftHom, algHomKaehlerMap_comp,
          hf, map_zero]
      have hright : algHomKaehlerMap Φ
          (algHomKaehlerMap
            (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A) w) = 0 := by
        rw [← algHomKaehlerMap_comp, hrightHom, algHomKaehlerMap_comp,
          ih, map_zero]
      change algHomKaehlerMap
        ((tensorAlgHom f (iteratedProductMap f m)).comp
          (Bialgebra.comulAlgHom k A)) w = 0
      rw [algHomKaehlerMap_comp, hcomul, map_add]
      change algHomKaehlerMap Φ
          (algHomKaehlerMap
              (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A) w) +
            algHomKaehlerMap Φ
              (algHomKaehlerMap
                (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A) w) = 0
      rw [hleft, hright, add_zero]

end

end GaloisForLFunctions.HTGeometry
