import GaloisForLFunctions.HTGeometry.ABHN.AzumayaTensorProduct
import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtensionBrauer

/-!
# Scalar extension preserves Brauer tensor addition

The base change of a tensor product is canonically the tensor product of the two base changes.
This makes every scalar-extension map on Brauer quotients compatible with tensor-product addition.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u

/-- Scalar extension distributes over an algebra tensor product. -/
noncomputable def scalarExtension_tensorProductAlgEquiv
    {K L A B : Type*} [Field K] [Field L] [Algebra K L]
    [Ring A] [Ring B] [Algebra K A] [Algebra K B] :
    L ⊗[K] (A ⊗[K] B) ≃ₐ[L] (L ⊗[K] A) ⊗[L] (L ⊗[K] B) :=
  (Algebra.TensorProduct.assoc K K L L A B).symm.trans <|
  (Algebra.TensorProduct.congr
    (Algebra.TensorProduct.rid L L (L ⊗[K] A)).symm (AlgEquiv.refl)).trans <|
  Algebra.TensorProduct.assoc K L L (L ⊗[K] A) L B

/-- Scalar extension of a tensor-product central simple representative has the same Brauer class
as the tensor product of the scalar extensions. -/
theorem brauerClass_scalarExtension_tensorProductCSA_eq
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (A B : CSA.{u, u} K) :
    brauerClass (scalarExtensionCSA (L := L) (tensorProductCSA A B)) =
      brauerClass (tensorProductCSA (scalarExtensionCSA (L := L) A)
        (scalarExtensionCSA (L := L) B)) :=
  brauerClass_eq_of_algEquiv _ _
    (scalarExtension_tensorProductAlgEquiv (K := K) (L := L)
      (A := A.carrier) (B := B.carrier))

/-- Scalar extension preserves tensor-product addition of Brauer classes. -/
theorem scalarExtensionBrauerMap_tensorAdd
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (x y : BrauerGroup.{u, u} K) :
    scalarExtensionBrauerMap K L (brauerTensorAdd K x y) =
      brauerTensorAdd L (scalarExtensionBrauerMap K L x)
        (scalarExtensionBrauerMap K L y) := by
  refine Quotient.inductionOn x ?_
  intro A
  refine Quotient.inductionOn y ?_
  intro B
  change scalarExtensionBrauerMap K L
      (brauerTensorAdd K (brauerClass A) (brauerClass B)) =
    brauerTensorAdd L (scalarExtensionBrauerMap K L (brauerClass A))
      (scalarExtensionBrauerMap K L (brauerClass B))
  simp only [brauerTensorAdd_brauerClass, scalarExtensionBrauerMap_brauerClass]
  exact brauerClass_scalarExtension_tensorProductCSA_eq K L A B

end GaloisForLFunctions.HTGeometry.ABHN
