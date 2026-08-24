import Mathlib.CategoryTheory.Triangulated.Generators
import Mathlib.CategoryTheory.Shift.Localization

/-!
# Functorial descent between Verdier quotients

A triangulated functor carrying one thick object property into another maps the corresponding
Verdier morphism classes. It therefore induces a shift-compatible triangulated functor between
the localizations.
-/

open CategoryTheory Limits Pretriangulated

namespace GaloisForLFunctions.IrregularStokes.VerdierFunctor

noncomputable section

variable {C D : Type*} [Category* C] [Category* D]
variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
variable [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
variable [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
variable (P : ObjectProperty C) (Q : ObjectProperty D)
variable [P.IsTriangulated] [Q.IsTriangulated]
variable [P.IsClosedUnderIsomorphisms] [Q.IsClosedUnderIsomorphisms]
variable (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]

/-- A triangulated functor preserving negligible objects maps the associated Verdier classes. -/
abbrev verdierLocalizerMorphism (hF : P ≤ Q.inverseImage F) :
    LocalizerMorphism P.trW Q.trW where
  functor := F
  map X Y f hf := by
    change Q.trW (F.map f)
    apply (Q.inverseImage_trW_iff F f).mp
    exact ObjectProperty.trW_monotone hF _ hf

/-- Functor induced between Verdier localizations by preservation of negligible objects. -/
noncomputable abbrev mapVerdierQuotient (hF : P ≤ Q.inverseImage F) :
    P.trW.Localization ⥤ Q.trW.Localization :=
  (verdierLocalizerMorphism P Q F hF).localizedFunctor P.trW.Q Q.trW.Q

/-- Canonical comparison square for the functor induced on Verdier localizations. -/
noncomputable abbrev mapVerdierQuotientSquare (hF : P ≤ Q.inverseImage F) :
    F ⋙ Q.trW.Q ≅ P.trW.Q ⋙ mapVerdierQuotient P Q F hF := by
  letI := LocalizerMorphism.catCommSq
    (verdierLocalizerMorphism P Q F hF) P.trW.Q Q.trW.Q
  exact CatCommSq.iso (verdierLocalizerMorphism P Q F hF).functor P.trW.Q Q.trW.Q
    ((verdierLocalizerMorphism P Q F hF).localizedFunctor P.trW.Q Q.trW.Q)

noncomputable instance mapVerdierQuotientSquare_hom_commShift
    (hF : P ≤ Q.inverseImage F) :
    NatTrans.CommShift (mapVerdierQuotientSquare P Q F hF).hom ℤ := by
  exact LocalizerMorphism.natTransCommShift_hom
    (verdierLocalizerMorphism P Q F hF) P.trW.Q Q.trW.Q
      (mapVerdierQuotient P Q F hF) (mapVerdierQuotientSquare P Q F hF)

/-- The functor induced between Verdier localizations is triangulated. -/
noncomputable instance mapVerdierQuotient_isTriangulated (hF : P ≤ Q.inverseImage F) :
    (mapVerdierQuotient P Q F hF).IsTriangulated := by
  letI : P.trW.Q.mapArrow.EssSurj :=
    Localization.essSurj_mapArrow P.trW.Q P.trW
  apply Functor.isTriangulated_of_precomp_iso (mapVerdierQuotientSquare P Q F hF).symm

end


end GaloisForLFunctions.IrregularStokes.VerdierFunctor
