/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.AzumayaGenericFiber
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldBrauer
import GaloisForLFunctions.HTGeometry.ABHN.LocalFieldResidueBrauer
import GaloisForLFunctions.HTGeometry.ABHN.LaurentSeriesFiniteLocalField
import GaloisForLFunctions.HTGeometry.ABHN.NumberFieldFiniteLocalField
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionFiniteLocalField
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionInfinityCompletion

/-!
# Finite residue fibers of Azumaya algebras

An Azumaya algebra over a commutative ring has a central simple fiber over every field-valued
point. When that point has finite residue field, the fiber is split because the Brauer group of a
finite field vanishes. This provides the finite-residue endpoint of the unramified part of a
Hasse-style local-global decomposition.

The result applies directly to local rings, nonarchimedean local-field valuation rings, finite
places of number fields, and closed points of global-function-field affine lines. It does not
identify a completed generic fiber with its residue fiber; that complete-DVR Brauer comparison is
the remaining local bridge toward finite ramification in ABHN.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped LaurentSeries ValuativeRel TensorProduct Polynomial
open IsDedekindDomain

universe u

noncomputable section

/-- The field fiber of an Azumaya algebra at a finite field is split. -/
theorem azumayaScalarExtensionBrauerClass_eq_split_of_finite
    (R S A : Type u) [CommRing R] [Field S] [Finite S] [Ring A]
    [Algebra R S] [Algebra R A] [IsAzumaya R A] :
    azumayaScalarExtensionBrauerClass R S A = brauerSplitClass S := by
  exact finiteField_brauerClass_eq_split S (azumayaScalarExtensionCSA R S A)

/-- The residue-field fiber of an Azumaya algebra over a local ring with finite residue field is
split. -/
theorem azumayaResidueBrauerClass_eq_split
    (R A : Type u) [CommRing R] [IsLocalRing R] [Finite (IsLocalRing.ResidueField R)]
    [Ring A] [Algebra R A] [IsAzumaya R A] :
    azumayaScalarExtensionBrauerClass R (IsLocalRing.ResidueField R) A =
      brauerSplitClass (IsLocalRing.ResidueField R) := by
  exact azumayaScalarExtensionBrauerClass_eq_split_of_finite R (IsLocalRing.ResidueField R) A

/-- After base change of an Azumaya algebra to a local ring with finite residue field, its residue
fiber is split. -/
theorem azumayaLocalBaseChangeResidueBrauerClass_eq_split
    (R S A : Type u) [CommRing R] [CommRing S] [IsLocalRing S]
    [Finite (IsLocalRing.ResidueField S)] [Ring A] [Algebra R S] [Algebra R A]
    [IsAzumaya R A] :
    letI : IsAzumaya S (S ⊗[R] A) :=
      AzumayaScalarExtension.isAzumaya_scalarExtension (R := R) (S := S) (A := A)
    azumayaScalarExtensionBrauerClass S (IsLocalRing.ResidueField S) (S ⊗[R] A) =
      brauerSplitClass (IsLocalRing.ResidueField S) := by
  letI : IsAzumaya S (S ⊗[R] A) :=
    AzumayaScalarExtension.isAzumaya_scalarExtension (R := R) (S := S) (A := A)
  exact azumayaResidueBrauerClass_eq_split S (S ⊗[R] A)

/-- The residue fiber of an Azumaya algebra over the valuation ring of a nonarchimedean local
field is split. -/
theorem nonarchimedeanLocalField_azumayaResidueBrauerClass_eq_split
    (K A : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Ring A] [Algebra 𝒪[K] A] [IsAzumaya 𝒪[K] A] :
    azumayaScalarExtensionBrauerClass 𝒪[K] 𝓀[K] A = brauerSplitClass 𝓀[K] := by
  exact azumayaResidueBrauerClass_eq_split 𝒪[K] A

open scoped NumberField

attribute [local instance] Ideal.Quotient.field

/-- The fiber of an Azumaya algebra over the ring of integers of a number field at every finite
place is split. -/
theorem numberFieldFinitePlace_azumayaResidueBrauerClass_eq_split
    (K A : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K)
    [Ring A] [Algebra (𝓞 K) A] [IsAzumaya (𝓞 K) A] :
    azumayaScalarExtensionBrauerClass (𝓞 K) (𝓞 K ⧸ v.maximalIdeal.asIdeal) A =
      brauerSplitClass (𝓞 K ⧸ v.maximalIdeal.asIdeal) := by
  letI : Finite (𝓞 K ⧸ v.maximalIdeal.asIdeal) :=
    GaloisForLFunctions.HTGeometry.finite_quotient_asIdeal K v.maximalIdeal
  exact azumayaScalarExtensionBrauerClass_eq_split_of_finite (𝓞 K)
    (𝓞 K ⧸ v.maximalIdeal.asIdeal) A

/-- The fiber of an Azumaya algebra over a global-function-field affine line at every closed
point is split. -/
theorem rationalFunctionFinitePlace_azumayaResidueBrauerClass_eq_split
    (F A : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X])
    [Ring A] [Algebra F[X] A] [IsAzumaya F[X] A] :
    azumayaScalarExtensionBrauerClass F[X] (F[X] ⧸ v.asIdeal) A =
      brauerSplitClass (F[X] ⧸ v.asIdeal) := by
  letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  exact azumayaScalarExtensionBrauerClass_eq_split_of_finite F[X] (F[X] ⧸ v.asIdeal) A

/-- The residue fiber of an Azumaya algebra over every finite completion of a number field is
split. This is the complete-local-field form of the finite-residue endpoint. -/
theorem numberFieldFinitePlaceCompletion_azumayaResidueBrauerClass_eq_split
    (K A : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K)
    [Ring A] [Algebra 𝒪[completion K (.finite v)] A]
    [IsAzumaya 𝒪[completion K (.finite v)] A] :
    azumayaScalarExtensionBrauerClass 𝒪[completion K (.finite v)]
      𝓀[completion K (.finite v)] A = brauerSplitClass 𝓀[completion K (.finite v)] := by
  exact azumayaResidueBrauerClass_eq_split 𝒪[completion K (.finite v)] A

/-- The residue fiber of an Azumaya algebra over every finite completion of `F(t)` is split. -/
theorem rationalFunctionFinitePlaceCompletion_azumayaResidueBrauerClass_eq_split
    (F A : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X])
    [Ring A] [Algebra 𝒪[rationalFunctionCompletion F (.finite v)] A]
    [IsAzumaya 𝒪[rationalFunctionCompletion F (.finite v)] A] :
    azumayaScalarExtensionBrauerClass 𝒪[rationalFunctionCompletion F (.finite v)]
      𝓀[rationalFunctionCompletion F (.finite v)] A =
        brauerSplitClass 𝓀[rationalFunctionCompletion F (.finite v)] := by
  exact azumayaResidueBrauerClass_eq_split
    𝒪[rationalFunctionCompletion F (.finite v)] A

/-- The residue fiber of an Azumaya algebra over the infinite completion of `F(t)` is split. -/
theorem rationalFunctionInfinitePlaceCompletion_azumayaResidueBrauerClass_eq_split
    (F A : Type u) [Field F] [Finite F] [Ring A]
    [Algebra 𝒪[rationalFunctionCompletion F .infinite] A]
    [IsAzumaya 𝒪[rationalFunctionCompletion F .infinite] A] :
    azumayaScalarExtensionBrauerClass 𝒪[rationalFunctionCompletion F .infinite]
      𝓀[rationalFunctionCompletion F .infinite] A =
        brauerSplitClass 𝓀[rationalFunctionCompletion F .infinite] := by
  exact azumayaResidueBrauerClass_eq_split
    𝒪[rationalFunctionCompletion F .infinite] A

/-- The residue fiber of an Azumaya algebra over a finite-coefficient Laurent-series valuation
ring is split. -/
theorem laurentSeries_azumayaResidueBrauerClass_eq_split
    (F A : Type u) [Field F] [Finite F] [Ring A] [Algebra 𝒪[F⸨X⸩] A]
    [IsAzumaya 𝒪[F⸨X⸩] A] :
    azumayaScalarExtensionBrauerClass 𝒪[F⸨X⸩] 𝓀[F⸨X⸩] A =
      brauerSplitClass 𝓀[F⸨X⸩] := by
  exact azumayaResidueBrauerClass_eq_split 𝒪[F⸨X⸩] A

end

end GaloisForLFunctions.HTGeometry.ABHN
