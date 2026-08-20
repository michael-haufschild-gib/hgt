import GaloisForLFunctions.HTGeometry.ABHN.AzumayaBaseChange
import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtension
import Mathlib.RingTheory.MatrixAlgebra

/-!
# Scalar extension on Brauer classes

The scalar extension of a central simple algebra is central simple by the Azumaya base-change
theorem.  This file proves that scalar extension also preserves Brauer equivalence, so it descends
to a genuine map of Brauer quotients.  This is the algebraic input needed for every global-to-local
Brauer map in Albert--Brauer--Hasse--Noether.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u

/-- Base change transports algebra equivalences. -/
noncomputable def scalarExtension_algEquiv
    {K L A B : Type*} [Field K] [Field L] [Algebra K L]
    [Ring A] [Ring B] [Algebra K A] [Algebra K B] (e : A ≃ₐ[K] B) :
    L ⊗[K] A ≃ₐ[L] L ⊗[K] B :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.map (AlgHom.id L L) e.toAlgHom)
    (Algebra.TensorProduct.map (AlgHom.id L L) e.symm.toAlgHom)
    (by ext x; simp)
    (by ext x; simp)

/-- Moving a matrix factor past scalar extension, as an algebra equivalence over the extended
field. -/
noncomputable def scalarExtension_matrixTensorAlgEquiv
    {K L A : Type*} [Field K] [Field L] [Algebra K L]
    [Ring A] [Algebra K A] (n : Type*) [Fintype n] [DecidableEq n] :
    ((L ⊗[K] A) ⊗[K] Matrix n n K) ≃ₐ[L] Matrix n n (L ⊗[K] A) where
  toFun := MatrixEquivTensor.toFunAlgHom n K (L ⊗[K] A)
  invFun := MatrixEquivTensor.invFun n K (L ⊗[K] A)
  left_inv := MatrixEquivTensor.left_inv n K (L ⊗[K] A)
  right_inv := MatrixEquivTensor.right_inv n K (L ⊗[K] A)
  map_mul' := map_mul (MatrixEquivTensor.toFunAlgHom n K (L ⊗[K] A))
  map_add' := map_add (MatrixEquivTensor.toFunAlgHom n K (L ⊗[K] A))
  commutes' l := by
    change MatrixEquivTensor.toFunAlgHom n K (L ⊗[K] A)
      ((algebraMap L (L ⊗[K] A) l) ⊗ₜ (1 : Matrix n n K)) = _
    rw [Algebra.TensorProduct.algebraMap_apply]
    rw [MatrixEquivTensor.toFunAlgHom_apply, Algebra.algebraMap_eq_smul_one]
    rw [Algebra.algebraMap_eq_smul_one]
    ext i j
    by_cases h : i = j
    · subst j
      simp
      change l ⊗ₜ[K] (1 : A) = l • (1 : L ⊗[K] A)
      rw [← Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.algebraMap_apply]
      simp
    · simp [h]

/-- Scalar extension commutes with stabilizing a central simple algebra by a square matrix
factor. -/
noncomputable def scalarExtension_matrixAlgEquiv
    {K L A : Type*} [Field K] [Field L] [Algebra K L]
    [Ring A] [Algebra K A] (n : Type*) [Fintype n] [DecidableEq n] :
    L ⊗[K] Matrix n n A ≃ₐ[L] Matrix n n (L ⊗[K] A) :=
  (scalarExtension_algEquiv (matrixEquivTensor n K A)).trans <|
    (Algebra.TensorProduct.assoc K K L L A (Matrix n n K)).symm.trans <|
      scalarExtension_matrixTensorAlgEquiv n

/-- The scalar extension of a central simple algebra, packaged over the extended field. -/
noncomputable def scalarExtensionCSA {K L : Type u} [Field K] [Field L] [Algebra K L]
    (A : CSA K) : CSA L where
  carrier := L ⊗[K] A.carrier
  isCentral := scalarExtensionAlg_isCentral A
  isSimple := scalarExtension_isSimpleRing A
  fin_dim := scalarExtensionAlg_finiteDimensional A

/-- Scalar extension preserves the matrix-stabilization relation defining the Brauer quotient. -/
theorem scalarExtension_isBrauerEquivalent {K L : Type u} [Field K] [Field L] [Algebra K L]
    (A B : CSA K) (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (scalarExtensionCSA (L := L) A) (scalarExtensionCSA (L := L) B) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  refine ⟨n, m, hn, hm, ?_⟩
  refine ⟨(scalarExtension_matrixAlgEquiv (K := K) (L := L) (A := A.carrier)
    (Fin n)).symm.trans ?_⟩
  refine (scalarExtension_algEquiv (L := L) e).trans ?_
  exact scalarExtension_matrixAlgEquiv (K := K) (L := L) (A := B.carrier) (Fin m)

/-- Scalar extension on Brauer quotients.  It is well-defined because it respects Brauer
equivalence, not merely equality of representatives. -/
noncomputable def scalarExtensionBrauerMap (K L : Type u) [Field K] [Field L] [Algebra K L] :
    BrauerGroup.{u, u} K → BrauerGroup.{u, u} L :=
  Quotient.lift
    (fun A ↦ brauerClass (scalarExtensionCSA (L := L) A))
    (by
      intro A B h
      exact Quotient.sound (scalarExtension_isBrauerEquivalent (L := L) A B h))

/-- Scalar extension on a represented Brauer class is represented by scalar extension. -/
theorem scalarExtensionBrauerMap_brauerClass (K L : Type u) [Field K] [Field L] [Algebra K L]
    (A : CSA K) :
    scalarExtensionBrauerMap K L (brauerClass A) = brauerClass (scalarExtensionCSA (L := L) A) :=
  rfl

/-- Scalar extension sends the split Brauer class to the split Brauer class. -/
theorem scalarExtensionBrauerMap_split (K L : Type u) [Field K] [Field L] [Algebra K L] :
    scalarExtensionBrauerMap K L (brauerSplitClass K) = brauerSplitClass L := by
  change brauerClass (scalarExtensionCSA (L := L) (scalarCSA K)) = brauerSplitClass L
  calc
    brauerClass (scalarExtensionCSA (L := L) (scalarCSA K)) =
        brauerClass (scalarExtensionMatrixFinScalarCSA K L 1) :=
      brauerClass_eq_of_algEquiv _ _
        (scalarExtension_algEquiv (L := L) (oneByOneMatrixAlgEquiv K K).symm)
    _ = brauerSplitClass L :=
      brauerClass_scalarExtensionMatrixFinScalar_eq (K := K) (L := L) 1

end GaloisForLFunctions.HTGeometry.ABHN
