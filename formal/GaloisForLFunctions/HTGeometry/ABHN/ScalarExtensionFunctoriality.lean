import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtensionTensorProduct

/-!
# Functoriality of scalar extension on Brauer groups

Successive scalar extensions are canonically equivalent to direct scalar extension.  On Brauer
classes this supplies identity and composition laws for the additive maps used by localization.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u

/-- Successive scalar extension is direct scalar extension, at the algebra level. -/
noncomputable def scalarExtension_transAlgEquiv
    {K L M A : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [Ring A] [Algebra K A] :
    M ⊗[L] (L ⊗[K] A) ≃ₐ[M] M ⊗[K] A :=
  (Algebra.TensorProduct.assoc K L M M L A).symm.trans <|
    Algebra.TensorProduct.congr (Algebra.TensorProduct.rid L M M) (AlgEquiv.refl)

/-- Successive scalar extension and direct scalar extension have the same Brauer class. -/
theorem brauerClass_scalarExtension_trans_eq
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (A : CSA.{u, u} K) :
    brauerClass (scalarExtensionCSA (L := M) (scalarExtensionCSA (L := L) A)) =
      brauerClass (scalarExtensionCSA (L := M) A) :=
  brauerClass_eq_of_algEquiv _ _
    (scalarExtension_transAlgEquiv (K := K) (L := L) (M := M) (A := A.carrier))

/-- Scalar extension composes on Brauer quotients. -/
theorem scalarExtensionBrauerMap_comp
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (x : BrauerGroup.{u, u} K) :
    scalarExtensionBrauerMap L M (scalarExtensionBrauerMap K L x) =
      scalarExtensionBrauerMap K M x := by
  refine Quotient.inductionOn x ?_
  intro A
  exact brauerClass_scalarExtension_trans_eq K L M A

/-- Identity scalar extension is the identity on Brauer classes. -/
theorem scalarExtensionBrauerMap_id (K : Type u) [Field K] (x : BrauerGroup.{u, u} K) :
    scalarExtensionBrauerMap K K x = x := by
  refine Quotient.inductionOn x ?_
  intro A
  exact brauerClass_eq_of_algEquiv _ _ (Algebra.TensorProduct.lid K A.carrier)

/-- The additive scalar-extension maps compose. -/
theorem scalarExtensionBrauerAddHom_comp
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    (scalarExtensionBrauerAddHom L M).comp (scalarExtensionBrauerAddHom K L) =
      scalarExtensionBrauerAddHom K M := by
  ext x
  exact scalarExtensionBrauerMap_comp K L M x

/-- The additive map of identity scalar extension is the identity homomorphism. -/
theorem scalarExtensionBrauerAddHom_id (K : Type u) [Field K] :
    scalarExtensionBrauerAddHom K K = AddMonoidHom.id (BrauerGroup.{u, u} K) := by
  ext x
  exact scalarExtensionBrauerMap_id K x

/-- Scalar extension commutes with the inverse represented by the opposite algebra. -/
theorem scalarExtensionBrauerMap_tensorNeg
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (x : BrauerGroup.{u, u} K) :
    scalarExtensionBrauerMap K L (brauerTensorNeg K x) =
      brauerTensorNeg L (scalarExtensionBrauerMap K L x) :=
  (scalarExtensionBrauerAddHom K L).map_neg x

end GaloisForLFunctions.HTGeometry.ABHN
