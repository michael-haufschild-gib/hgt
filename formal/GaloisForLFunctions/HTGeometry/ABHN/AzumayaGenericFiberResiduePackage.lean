import GaloisForLFunctions.HTGeometry.ABHN.AzumayaFiniteResidueFiber
import GaloisForLFunctions.HTGeometry.ABHN.AzumayaEnvelopeBaseChange
import GaloisForLFunctions.HTGeometry.ABHN.AzumayaScalarExtension

/-!
# Generic fibers and finite residue fibers under scalar extension

Two compatible scalar extensions of an Azumaya algebra retain its original generic fiber after
extension to a field.  When the second base is local with finite residue field, its residue
Brauer fiber is split.  This packages the pre-Henselian local datum used by finite-ramification
arguments without identifying residue and completed-field Brauer classes.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u

noncomputable section

/-- A two-step scalar extension of an Azumaya algebra with its unchanged final generic fiber and
split finite residue fiber. -/
structure AzumayaGenericFiberResiduePackage
    (R S V K B : Type u) [CommRing R] [CommRing S] [CommRing V] [Field K]
    [Algebra R S] [Algebra S V] [Algebra R K] [Algebra S K] [Algebra V K]
    [IsScalarTower R S K] [IsScalarTower S V K]
    [Ring B] [Algebra R B] [IsLocalRing V]
    [IsAzumaya V (V ⊗[S] (S ⊗[R] B))] where
  genericFiber : K ⊗[V] (V ⊗[S] (S ⊗[R] B)) ≃ₐ[K] K ⊗[R] B
  residueSplit : azumayaScalarExtensionBrauerClass V (IsLocalRing.ResidueField V)
    (V ⊗[S] (S ⊗[R] B)) = brauerSplitClass (IsLocalRing.ResidueField V)

/-- Construct the generic-fiber and finite-residue package for successive scalar extensions of
an Azumaya algebra. -/
noncomputable def azumayaScalarExtension_genericFiber_residuePackage
    (R S V K B : Type u) [CommRing R] [CommRing S] [CommRing V] [Field K]
    [Algebra R S] [Algebra S V] [Algebra R K] [Algebra S K] [Algebra V K]
    [IsScalarTower R S K] [IsScalarTower S V K]
    [Ring B] [Algebra R B] [IsAzumaya R B]
    [IsLocalRing V]
    [Finite (IsLocalRing.ResidueField V)] :
    letI : IsAzumaya S (S ⊗[R] B) :=
      AzumayaScalarExtension.isAzumaya_scalarExtension (R := R) (S := S) (A := B)
    letI : IsAzumaya V (V ⊗[S] (S ⊗[R] B)) :=
      AzumayaScalarExtension.isAzumaya_scalarExtension (R := S) (S := V) (A := S ⊗[R] B)
    AzumayaGenericFiberResiduePackage R S V K B := by
  letI : IsAzumaya S (S ⊗[R] B) :=
    AzumayaScalarExtension.isAzumaya_scalarExtension (R := R) (S := S) (A := B)
  letI : IsAzumaya V (V ⊗[S] (S ⊗[R] B)) :=
    AzumayaScalarExtension.isAzumaya_scalarExtension (R := S) (S := V) (A := S ⊗[R] B)
  exact {
    genericFiber := (AzumayaScalarExtension.cancelBaseChangeNoncommutative
      (R := S) (S := V) (A := S ⊗[R] B) (T := K)).trans
        (AzumayaScalarExtension.cancelBaseChangeNoncommutative
          (R := R) (S := S) (A := B) (T := K))
    residueSplit := azumayaResidueBrauerClass_eq_split V (V ⊗[S] (S ⊗[R] B)) }

end

end GaloisForLFunctions.HTGeometry.ABHN
