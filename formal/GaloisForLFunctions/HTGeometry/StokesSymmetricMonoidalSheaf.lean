import GaloisForLFunctions.HTGeometry.StokesOrdinaryEpigraphConvolution
import Mathlib.CategoryTheory.Sites.Monoidal

/-!
# Symmetric monoidal structure behind ordinary Stokes sheaf tensor

Integer-module sheaves inherit a symmetric monoidal structure from monoidal localisation of
pointwise presheaf tensor. This file compares the existing underived `sheafTensorFunctor` with
that canonical tensor by a natural isomorphism and exposes its standard coherence isomorphisms.

This remains underived: no K-flat replacement, derived tensor, enhanced tensor, or irregular
Riemann--Hilbert equivalence is constructed here.
-/

namespace GaloisForLFunctions.IrregularStokes.MonoidalSheafTensor

open CategoryTheory
open OrdinaryConvolution
open scoped MonoidalCategory

/-- Sheafification with its source and target expressed through the `TopCat` aliases. -/
noncomputable def topPresheafToSheaf (Y : TopCat) :
    TopCat.Presheaf IntModuleCat Y ⥤ TopCat.Sheaf IntModuleCat Y :=
  CategoryTheory.presheafToSheaf (Opens.grothendieckTopology Y) IntModuleCat

/-- Forgetful functor from sheaves to presheaves, expressed through the `TopCat` aliases. -/
def topSheafToPresheaf (Y : TopCat) :
    TopCat.Sheaf IntModuleCat Y ⥤ TopCat.Presheaf IntModuleCat Y :=
  TopCat.Sheaf.forget IntModuleCat Y

/-- Explicitly typed copy of the existing forget--tensor--sheafify functor. -/
noncomputable def topSheafTensorFunctor (Y : TopCat) :
    TopCat.Sheaf IntModuleCat Y × TopCat.Sheaf IntModuleCat Y ⥤
      TopCat.Sheaf IntModuleCat Y := by
  letI pMon : MonoidalCategory (TopCat.Presheaf IntModuleCat Y) :=
    CategoryTheory.Monoidal.functorCategoryMonoidal
  exact (topSheafToPresheaf Y).prod (topSheafToPresheaf Y) ⋙
    MonoidalCategory.tensor _ ⋙ topPresheafToSheaf Y

/-- The explicitly typed tensor is definitionally the existing Stokes sheaf tensor. -/
theorem sheafTensorFunctor_eq_topSheafTensorFunctor (Y : TopCat) :
    sheafTensorFunctor Y = topSheafTensorFunctor Y := by
  rfl

/-- Tensor bifunctor of the monoidal localisation structure on integer-module sheaves. -/
noncomputable def canonicalSheafTensorFunctor (Y : TopCat) :
    TopCat.Sheaf IntModuleCat Y × TopCat.Sheaf IntModuleCat Y ⥤
      TopCat.Sheaf IntModuleCat Y := by
  letI pMon : MonoidalCategory (TopCat.Presheaf IntModuleCat Y) :=
    CategoryTheory.Monoidal.functorCategoryMonoidal
  letI sMon : MonoidalCategory (TopCat.Sheaf IntModuleCat Y) :=
    CategoryTheory.Sheaf.monoidalCategory
      (Opens.grothendieckTopology Y) IntModuleCat
  exact @MonoidalCategory.tensor _ _ sMon

/-- Tensor unit of the monoidal localisation structure. -/
noncomputable def canonicalSheafTensorUnit (Y : TopCat) :
    TopCat.Sheaf IntModuleCat Y := by
  letI pMon : MonoidalCategory (TopCat.Presheaf IntModuleCat Y) :=
    CategoryTheory.Monoidal.functorCategoryMonoidal
  letI sMon : MonoidalCategory (TopCat.Sheaf IntModuleCat Y) :=
    CategoryTheory.Sheaf.monoidalCategory
      (Opens.grothendieckTopology Y) IntModuleCat
  exact 𝟙_ _

/-- Associator inherited from monoidal localisation. -/
noncomputable def canonicalSheafTensorAssociator (Y : TopCat)
    (F G H : TopCat.Sheaf IntModuleCat Y) :
    (canonicalSheafTensorFunctor Y).obj
        ((canonicalSheafTensorFunctor Y).obj (F, G), H) ≅
      (canonicalSheafTensorFunctor Y).obj
        (F, (canonicalSheafTensorFunctor Y).obj (G, H)) := by
  letI pMon : MonoidalCategory (TopCat.Presheaf IntModuleCat Y) :=
    CategoryTheory.Monoidal.functorCategoryMonoidal
  letI sMon : MonoidalCategory (TopCat.Sheaf IntModuleCat Y) :=
    CategoryTheory.Sheaf.monoidalCategory
      (Opens.grothendieckTopology Y) IntModuleCat
  exact α_ F G H

/-- Left unitor inherited from monoidal localisation. -/
noncomputable def canonicalSheafTensorLeftUnitor (Y : TopCat)
    (F : TopCat.Sheaf IntModuleCat Y) :
    (canonicalSheafTensorFunctor Y).obj (canonicalSheafTensorUnit Y, F) ≅ F := by
  letI pMon : MonoidalCategory (TopCat.Presheaf IntModuleCat Y) :=
    CategoryTheory.Monoidal.functorCategoryMonoidal
  letI sMon : MonoidalCategory (TopCat.Sheaf IntModuleCat Y) :=
    CategoryTheory.Sheaf.monoidalCategory
      (Opens.grothendieckTopology Y) IntModuleCat
  exact λ_ F

/-- Right unitor inherited from monoidal localisation. -/
noncomputable def canonicalSheafTensorRightUnitor (Y : TopCat)
    (F : TopCat.Sheaf IntModuleCat Y) :
    (canonicalSheafTensorFunctor Y).obj (F, canonicalSheafTensorUnit Y) ≅ F := by
  letI pMon : MonoidalCategory (TopCat.Presheaf IntModuleCat Y) :=
    CategoryTheory.Monoidal.functorCategoryMonoidal
  letI sMon : MonoidalCategory (TopCat.Sheaf IntModuleCat Y) :=
    CategoryTheory.Sheaf.monoidalCategory
      (Opens.grothendieckTopology Y) IntModuleCat
  exact ρ_ F

/-- Symmetric braiding inherited from monoidal localisation. -/
noncomputable def canonicalSheafTensorBraiding (Y : TopCat)
    (F G : TopCat.Sheaf IntModuleCat Y) :
    (canonicalSheafTensorFunctor Y).obj (F, G) ≅
      (canonicalSheafTensorFunctor Y).obj (G, F) := by
  letI pMon : MonoidalCategory (TopCat.Presheaf IntModuleCat Y) :=
    CategoryTheory.Monoidal.functorCategoryMonoidal
  letI sMon : MonoidalCategory (TopCat.Sheaf IntModuleCat Y) :=
    CategoryTheory.Sheaf.monoidalCategory
      (Opens.grothendieckTopology Y) IntModuleCat
  letI sSym : SymmetricCategory (TopCat.Sheaf IntModuleCat Y) :=
    CategoryTheory.Sheaf.symmetricCategory
      (Opens.grothendieckTopology Y) IntModuleCat
  exact β_ F G

/-- Objectwise comparison: inverse sheafification tensorator, then tensor of counits. -/
noncomputable def sheafTensorObjIso (Y : TopCat)
    (F G : TopCat.Sheaf IntModuleCat Y) :
    (topSheafTensorFunctor Y).obj (F, G) ≅
      (canonicalSheafTensorFunctor Y).obj (F, G) := by
  letI pMon : MonoidalCategory (TopCat.Presheaf IntModuleCat Y) :=
    CategoryTheory.Monoidal.functorCategoryMonoidal
  letI sMon : MonoidalCategory (TopCat.Sheaf IntModuleCat Y) :=
    CategoryTheory.Sheaf.monoidalCategory
      (Opens.grothendieckTopology Y) IntModuleCat
  let L := topPresheafToSheaf Y
  let U := topSheafToPresheaf Y
  letI fMon : @CategoryTheory.Functor.Monoidal
      (TopCat.Presheaf IntModuleCat Y) _ pMon
      (TopCat.Sheaf IntModuleCat Y) _ sMon L := by
    dsimp [L, topPresheafToSheaf]
    exact
      CategoryTheory.Sheaf.instMonoidalFunctorOppositePresheafToSheaf
        (Opens.grothendieckTopology Y) IntModuleCat
  letI counitIsoF : IsIso ((CategoryTheory.sheafificationAdjunction
      (Opens.grothendieckTopology Y) IntModuleCat).counit.app F) :=
    CategoryTheory.isIso_sheafificationAdjunction_counit F
  letI counitIsoG : IsIso ((CategoryTheory.sheafificationAdjunction
      (Opens.grothendieckTopology Y) IntModuleCat).counit.app G) :=
    CategoryTheory.isIso_sheafificationAdjunction_counit G
  exact (@CategoryTheory.Functor.Monoidal.μIso
      (TopCat.Presheaf IntModuleCat Y) _ pMon
      (TopCat.Sheaf IntModuleCat Y) _ sMon L fMon
      (U.obj F) (U.obj G)).symm ≪≫
    @MonoidalCategory.tensorIso _ _ sMon _ _ _ _
      (@asIso _ _ _ _ ((CategoryTheory.sheafificationAdjunction
        (Opens.grothendieckTopology Y) IntModuleCat).counit.app F) counitIsoF)
      (@asIso _ _ _ _ ((CategoryTheory.sheafificationAdjunction
        (Opens.grothendieckTopology Y) IntModuleCat).counit.app G) counitIsoG)

set_option backward.isDefEq.respectTransparency false in
/-- Natural comparison between the typed forget--tensor--sheafify functor and canonical tensor. -/
noncomputable def topSheafTensorIsoCanonical (Y : TopCat) :
    topSheafTensorFunctor Y ≅ canonicalSheafTensorFunctor Y :=
  NatIso.ofComponents
    (fun FG => sheafTensorObjIso Y FG.1 FG.2)
    (fun {X Z} f => by
      letI pMon : MonoidalCategory (TopCat.Presheaf IntModuleCat Y) :=
        CategoryTheory.Monoidal.functorCategoryMonoidal
      letI sMon : MonoidalCategory (TopCat.Sheaf IntModuleCat Y) :=
        CategoryTheory.Sheaf.monoidalCategory
          (Opens.grothendieckTopology Y) IntModuleCat
      letI sStruct : MonoidalCategoryStruct (TopCat.Sheaf IntModuleCat Y) :=
        @MonoidalCategory.toMonoidalCategoryStruct _ _ sMon
      let L := topPresheafToSheaf Y
      let U := topSheafToPresheaf Y
      letI fMon : @CategoryTheory.Functor.Monoidal
          (TopCat.Presheaf IntModuleCat Y) _ pMon
          (TopCat.Sheaf IntModuleCat Y) _ sMon L := by
        dsimp [L, topPresheafToSheaf]
        exact
          CategoryTheory.Sheaf.instMonoidalFunctorOppositePresheafToSheaf
            (Opens.grothendieckTopology Y) IntModuleCat
      rcases X with ⟨F, G⟩
      rcases Z with ⟨F', G'⟩
      rcases f with ⟨f, g⟩
      let tensorHomS := fun {A B C D : TopCat.Sheaf IntModuleCat Y}
          (a : A ⟶ B) (b : C ⟶ D) =>
        @MonoidalCategoryStruct.tensorHom _ _ sStruct A B C D a b
      dsimp [sheafTensorObjIso, canonicalSheafTensorFunctor, topSheafTensorFunctor]
      simp
      have hδ := @CategoryTheory.Functor.OplaxMonoidal.δ_natural_assoc
        (TopCat.Presheaf IntModuleCat Y) _ pMon
        (TopCat.Sheaf IntModuleCat Y) _ sMon
        L CategoryTheory.Functor.Monoidal.toOplaxMonoidal
        F.obj F'.obj G.obj G'.obj (U.map f) (U.map g) _
        (tensorHomS
          ((CategoryTheory.sheafificationAdjunction
            (Opens.grothendieckTopology Y) IntModuleCat).counit.app F')
          ((CategoryTheory.sheafificationAdjunction
            (Opens.grothendieckTopology Y) IntModuleCat).counit.app G'))
      have hf : L.map (U.map f) ≫
          (CategoryTheory.sheafificationAdjunction
            (Opens.grothendieckTopology Y) IntModuleCat).counit.app F' =
          (CategoryTheory.sheafificationAdjunction
            (Opens.grothendieckTopology Y) IntModuleCat).counit.app F ≫ f := by
        simpa [L, U, topPresheafToSheaf, topSheafToPresheaf,
          TopCat.Sheaf.forget] using
          (CategoryTheory.sheafificationAdjunction
            (Opens.grothendieckTopology Y) IntModuleCat).counit.naturality f
      have hg : L.map (U.map g) ≫
          (CategoryTheory.sheafificationAdjunction
            (Opens.grothendieckTopology Y) IntModuleCat).counit.app G' =
          (CategoryTheory.sheafificationAdjunction
            (Opens.grothendieckTopology Y) IntModuleCat).counit.app G ≫ g := by
        simpa [L, U, topPresheafToSheaf, topSheafToPresheaf,
          TopCat.Sheaf.forget] using
          (CategoryTheory.sheafificationAdjunction
            (Opens.grothendieckTopology Y) IntModuleCat).counit.naturality g
      have htensor :
          tensorHomS (L.map (U.map f)) (L.map (U.map g)) ≫
              tensorHomS
                ((CategoryTheory.sheafificationAdjunction
                  (Opens.grothendieckTopology Y) IntModuleCat).counit.app F')
                ((CategoryTheory.sheafificationAdjunction
                  (Opens.grothendieckTopology Y) IntModuleCat).counit.app G') =
            tensorHomS
                ((CategoryTheory.sheafificationAdjunction
                  (Opens.grothendieckTopology Y) IntModuleCat).counit.app F)
                ((CategoryTheory.sheafificationAdjunction
                  (Opens.grothendieckTopology Y) IntModuleCat).counit.app G) ≫
              tensorHomS f g := by
        calc
          _ = tensorHomS
                (L.map (U.map f) ≫
                  (CategoryTheory.sheafificationAdjunction
                    (Opens.grothendieckTopology Y) IntModuleCat).counit.app F')
                (L.map (U.map g) ≫
                  (CategoryTheory.sheafificationAdjunction
                    (Opens.grothendieckTopology Y) IntModuleCat).counit.app G') :=
              @MonoidalCategory.tensorHom_comp_tensorHom
                (TopCat.Sheaf IntModuleCat Y) _ sMon _ _ _ _ _ _
                (L.map (U.map f)) (L.map (U.map g))
                ((CategoryTheory.sheafificationAdjunction
                  (Opens.grothendieckTopology Y) IntModuleCat).counit.app F')
                ((CategoryTheory.sheafificationAdjunction
                  (Opens.grothendieckTopology Y) IntModuleCat).counit.app G')
          _ = tensorHomS
                ((CategoryTheory.sheafificationAdjunction
                  (Opens.grothendieckTopology Y) IntModuleCat).counit.app F ≫ f)
                ((CategoryTheory.sheafificationAdjunction
                  (Opens.grothendieckTopology Y) IntModuleCat).counit.app G ≫ g) := by
              rw [hf, hg]
          _ = _ := (@MonoidalCategory.tensorHom_comp_tensorHom
              (TopCat.Sheaf IntModuleCat Y) _ sMon _ _ _ _ _ _
              ((CategoryTheory.sheafificationAdjunction
                (Opens.grothendieckTopology Y) IntModuleCat).counit.app F)
              ((CategoryTheory.sheafificationAdjunction
                (Opens.grothendieckTopology Y) IntModuleCat).counit.app G)
              f g).symm
      have hfinal :
          L.map (U.map f ⊗ₘ U.map g) ≫
                CategoryTheory.Functor.OplaxMonoidal.δ L F'.obj G'.obj ≫
              tensorHomS
                ((CategoryTheory.sheafificationAdjunction
                  (Opens.grothendieckTopology Y) IntModuleCat).counit.app F')
                ((CategoryTheory.sheafificationAdjunction
                  (Opens.grothendieckTopology Y) IntModuleCat).counit.app G') =
            CategoryTheory.Functor.OplaxMonoidal.δ L F.obj G.obj ≫
                tensorHomS
                  ((CategoryTheory.sheafificationAdjunction
                    (Opens.grothendieckTopology Y) IntModuleCat).counit.app F)
                  ((CategoryTheory.sheafificationAdjunction
                    (Opens.grothendieckTopology Y) IntModuleCat).counit.app G) ≫
              tensorHomS f g := by
        calc
          _ = CategoryTheory.Functor.OplaxMonoidal.δ L F.obj G.obj ≫
                tensorHomS (L.map (U.map f)) (L.map (U.map g)) ≫
                  tensorHomS
                    ((CategoryTheory.sheafificationAdjunction
                      (Opens.grothendieckTopology Y) IntModuleCat).counit.app F')
                    ((CategoryTheory.sheafificationAdjunction
                      (Opens.grothendieckTopology Y) IntModuleCat).counit.app G') := hδ.symm
          _ = CategoryTheory.Functor.OplaxMonoidal.δ L F.obj G.obj ≫
                (tensorHomS (L.map (U.map f)) (L.map (U.map g)) ≫
                  tensorHomS
                    ((CategoryTheory.sheafificationAdjunction
                      (Opens.grothendieckTopology Y) IntModuleCat).counit.app F')
                    ((CategoryTheory.sheafificationAdjunction
                      (Opens.grothendieckTopology Y) IntModuleCat).counit.app G')) :=
              Category.assoc _ _ _
          _ = CategoryTheory.Functor.OplaxMonoidal.δ L F.obj G.obj ≫
                (tensorHomS
                    ((CategoryTheory.sheafificationAdjunction
                      (Opens.grothendieckTopology Y) IntModuleCat).counit.app F)
                    ((CategoryTheory.sheafificationAdjunction
                      (Opens.grothendieckTopology Y) IntModuleCat).counit.app G) ≫
                  tensorHomS f g) := by rw [htensor]
          _ = _ := (Category.assoc _ _ _).symm
      simpa [L, U, tensorHomS, topSheafTensorFunctor, topSheafToPresheaf,
        TopCat.Sheaf.forget] using hfinal)

/-- Existing ordinary Stokes sheaf tensor is naturally isomorphic to canonical tensor. -/
noncomputable def sheafTensorIsoCanonical (Y : TopCat) :
    sheafTensorFunctor Y ≅ canonicalSheafTensorFunctor Y :=
  eqToIso (sheafTensorFunctor_eq_topSheafTensorFunctor Y) ≪≫
    topSheafTensorIsoCanonical Y

end GaloisForLFunctions.IrregularStokes.MonoidalSheafTensor
