import Mathlib.RingTheory.Localization.BaseChange

/-! Localizing either factor of a tensor product localizes the tensor
product at the corresponding copy of the multiplicative set. -/

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.PD

variable {k A B C : Type} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C] [Algebra A B] [IsScalarTower k A B]

/-- The algebra structure from the map on the left tensor factor. -/
abbrev tensorLeftChangeAlgebra : Algebra (A ⊗[k] C) (B ⊗[k] C) :=
  (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A B) (AlgHom.id k C)).toRingHom.toAlgebra

/-- The algebra structure from the map on the right tensor factor. -/
abbrev tensorRightChangeAlgebra : Algebra (C ⊗[k] A) (C ⊗[k] B) :=
  (Algebra.TensorProduct.map (AlgHom.id k C) (IsScalarTower.toAlgHom k A B)).toRingHom.toAlgebra

theorem isLocalization_tensorLeft (M : Submonoid A) [IsLocalization M B] :
    letI := tensorLeftChangeAlgebra (k := k) (A := A) (B := B) (C := C)
    IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[k] C) M) (B ⊗[k] C) := by
  let T := A ⊗[k] C
  let U := B ⊗[k] C
  let f : T →ₐ[k] U := Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A B) (AlgHom.id k C)
  letI : Algebra T U := tensorLeftChangeAlgebra
  letI : IsScalarTower A T U := .of_algebraMap_eq fun a => by
    change algebraMap A B a ⊗ₜ[k] (1 : C) = f (a ⊗ₜ[k] (1 : C))
    rw [show f (a ⊗ₜ[k] (1 : C)) = algebraMap A B a ⊗ₜ[k] (1 : C) from
      Algebra.TensorProduct.map_tmul _ _ _ _]
  refine IsLocalization.tensorProduct_tensorProduct k C M B ?_
  ext c
  change f ((1 : A) ⊗ₜ[k] c) = (1 : B) ⊗ₜ[k] c
  rw [show f ((1 : A) ⊗ₜ[k] c) = algebraMap A B (1 : A) ⊗ₜ[k] c from
    Algebra.TensorProduct.map_tmul _ _ _ _, map_one]

theorem isLocalization_tensorRight (M : Submonoid A) [IsLocalization M B] :
    letI := tensorRightChangeAlgebra (k := k) (A := A) (B := B) (C := C)
    IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := k) (A := C))) (C ⊗[k] B) := by
  let T := C ⊗[k] A
  let U := C ⊗[k] B
  let f : T →ₐ[k] U := Algebra.TensorProduct.map (AlgHom.id k C) (IsScalarTower.toAlgHom k A B)
  letI : Algebra T U := tensorRightChangeAlgebra
  letI : IsScalarTower C T U := .of_algebraMap_eq fun c => by
    change c ⊗ₜ[k] (1 : B) = f (c ⊗ₜ[k] (1 : A))
    rw [show f (c ⊗ₜ[k] (1 : A)) = c ⊗ₜ[k] algebraMap A B (1 : A) from
      Algebra.TensorProduct.map_tmul _ _ _ _, map_one]
  refine IsLocalization.tensorProduct_tensorProduct_right k C M B ?_
  ext a
  change f ((1 : C) ⊗ₜ[k] a) = (1 : C) ⊗ₜ[k] algebraMap A B a
  exact Algebra.TensorProduct.map_tmul _ _ _ _

end GlobalTheory.PD
