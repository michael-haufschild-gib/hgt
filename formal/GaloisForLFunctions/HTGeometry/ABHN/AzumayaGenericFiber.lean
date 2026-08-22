/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.AzumayaScalarExtension
import GaloisForLFunctions.HTGeometry.ABHN.CentralSimpleAzumaya
import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtensionBrauer

/-!
# Field fibers of Azumaya algebras

An Azumaya algebra over a commutative ring becomes a finite-dimensional central simple algebra
after scalar extension to any field. In particular, an Azumaya algebra over a Dedekind domain has
a canonical central simple generic fiber. This is the algebraic interface for an Azumaya order in
the finite-ramification part of Albert--Brauer--Hasse--Noether.

It does not construct Azumaya orders for arbitrary central simple algebras, nor does it identify
the Brauer class of a generic fiber at a completion with a residue-field class. Those are the
remaining arithmetic bridges.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u

noncomputable section

/-- The scalar extension of an Azumaya algebra to a field, packaged as a central simple algebra.
This applies in particular to the generic fiber of an Azumaya algebra over a domain. -/
noncomputable def azumayaScalarExtensionCSA (R S A : Type u) [CommRing R] [Field S] [Ring A]
    [Algebra R S] [Algebra R A] [IsAzumaya R A] : CSA S where
  carrier := S ⊗[R] A
  isCentral := by
    letI : IsAzumaya S (S ⊗[R] A) :=
      AzumayaScalarExtension.isAzumaya_scalarExtension (R := R) (S := S) (A := A)
    infer_instance
  isSimple := by
    letI : IsAzumaya S (S ⊗[R] A) :=
      AzumayaScalarExtension.isAzumaya_scalarExtension (R := R) (S := S) (A := A)
    exact isSimpleRing_of_isAzumaya (K := S) _
  fin_dim := by infer_instance

/-- The Brauer class of the field fiber of an Azumaya algebra. -/
noncomputable def azumayaScalarExtensionBrauerClass (R S A : Type u) [CommRing R] [Field S]
    [Ring A] [Algebra R S] [Algebra R A] [IsAzumaya R A] : BrauerGroup S :=
  brauerClass (azumayaScalarExtensionCSA R S A)

/-- The field fiber of the trivial Azumaya algebra is split. -/
theorem azumayaScalarExtensionBrauerClass_self (R S : Type u) [CommRing R] [Field S]
    [Algebra R S] : azumayaScalarExtensionBrauerClass R S R = brauerSplitClass S := by
  exact brauerClass_eq_of_algEquiv _ _ (Algebra.TensorProduct.rid R S S)

/-- Extending an Azumaya field fiber through a tower of fields agrees, on Brauer classes, with
forming the final field fiber directly from the original Azumaya algebra. -/
noncomputable def azumayaScalarExtensionTransAlgEquiv
    {R S T A : Type u} [CommRing R] [Field S] [Field T] [Ring A]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] [Algebra R A] :
    T ⊗[S] (S ⊗[R] A) ≃ₐ[T] T ⊗[R] A :=
  (Algebra.TensorProduct.assoc R S T T S A).symm.trans <|
    Algebra.TensorProduct.congr (Algebra.TensorProduct.rid S T T) (AlgEquiv.refl)

/-- The Brauer class of an Azumaya field fiber is functorial under a tower of field extensions. -/
theorem azumayaScalarExtensionBrauerClass_trans_eq
    (R S T A : Type u) [CommRing R] [Field S] [Field T] [Ring A]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] [Algebra R A]
    [IsAzumaya R A] :
    scalarExtensionBrauerMap S T (azumayaScalarExtensionBrauerClass R S A) =
      azumayaScalarExtensionBrauerClass R T A := by
  exact brauerClass_eq_of_algEquiv _ _ (azumayaScalarExtensionTransAlgEquiv)

/-- The central simple generic fiber of an Azumaya algebra over a domain. -/
noncomputable def azumayaFractionRingCSA (R A : Type u) [CommRing R] [IsDomain R] [Ring A]
    [Algebra R A] [IsAzumaya R A] : CSA (FractionRing R) :=
  azumayaScalarExtensionCSA R (FractionRing R) A

/-- The Brauer class of the generic fiber of an Azumaya algebra over a domain. -/
noncomputable def azumayaFractionRingBrauerClass (R A : Type u) [CommRing R] [IsDomain R]
    [Ring A] [Algebra R A] [IsAzumaya R A] : BrauerGroup (FractionRing R) :=
  azumayaScalarExtensionBrauerClass R (FractionRing R) A

/-- The generic fiber of the trivial Azumaya algebra is split. -/
theorem azumayaFractionRingBrauerClass_self (R : Type u) [CommRing R] [IsDomain R] :
    azumayaFractionRingBrauerClass R R = brauerSplitClass (FractionRing R) :=
  azumayaScalarExtensionBrauerClass_self R (FractionRing R)

end

end GaloisForLFunctions.HTGeometry.ABHN
