import GaloisForLFunctions.HTGeometry.StokesIndFunctorExtension
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Functoriality of covariant ind-extension

The presheaf-left-Kan-extension model of `Ind.map` respects natural isomorphisms, identity
functors, and composition. The proofs use uniqueness of left adjoints at presheaf level and then
cancel the fully faithful inclusion of ind-objects into presheaves.
-/

namespace CategoryTheory

open Functor

universe u

namespace Ind

variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- Naturally isomorphic base functors induce isomorphic presheaf precomposition functors. -/
noncomputable def precomposeIso {F G : C ⥤ D} (e : F ≅ G) :
    (whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u)).obj F.op ≅
      (whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u)).obj G.op :=
  NatIso.ofComponents (fun X => isoWhiskerRight (NatIso.op e).symm X) (fun α => by
    ext X x
    exact ConcreteCategory.congr_hom
      (α.naturality ((NatIso.op e).symm.hom.app X)).symm x)

/-- Naturally isomorphic base functors have isomorphic presheaf left Kan extensions. -/
noncomputable def lanNatIso {F G : C ⥤ D} (e : F ≅ G) :
    (F.op.lan : (Cᵒᵖ ⥤ Type u) ⥤ Dᵒᵖ ⥤ Type u) ≅
      (G.op.lan : (Cᵒᵖ ⥤ Type u) ⥤ Dᵒᵖ ⥤ Type u) :=
  ((F.op.lanAdjunction (Type u)).ofNatIsoRight
    (precomposeIso (C := C) (D := D) e)).leftAdjointUniq
      (G.op.lanAdjunction (Type u))

/-- Covariant ind-extension respects natural isomorphisms of base functors. -/
noncomputable def mapNatIso {F G : C ⥤ D} (e : F ≅ G) :
    Ind.map F ≅ Ind.map G :=
  Functor.fullyFaithfulCancelRight (Ind.inclusion D)
    (mapCompInclusionIso F ≪≫
      isoWhiskerLeft (Ind.inclusion C) (lanNatIso e) ≪≫
      (mapCompInclusionIso G).symm)

/-- Presheaf precomposition along the identity is naturally isomorphic to the identity. -/
noncomputable def precomposeIdIso :
    (whiskeringLeft Cᵒᵖ Cᵒᵖ (Type u)).obj (𝟭 C).op ≅
      𝟭 (Cᵒᵖ ⥤ Type u) :=
  NatIso.ofComponents (fun X =>
    isoWhiskerRight (Functor.opId C) X ≪≫ Functor.leftUnitor X)
    (fun α => by
      ext X x
      exact ConcreteCategory.congr_hom
        (α.naturality ((Functor.opId C).hom.app X)).symm x)

/-- Left Kan extension along the identity is naturally isomorphic to the identity. -/
noncomputable def lanIdIso :
    ((𝟭 C).op.lan : (Cᵒᵖ ⥤ Type u) ⥤ Cᵒᵖ ⥤ Type u) ≅
      𝟭 (Cᵒᵖ ⥤ Type u) :=
  (((𝟭 C).op.lanAdjunction (Type u)).ofNatIsoRight precomposeIdIso).leftAdjointUniq
    (Adjunction.id : (𝟭 (Cᵒᵖ ⥤ Type u)) ⊣ 𝟭 (Cᵒᵖ ⥤ Type u))

/-- Covariant ind-extension maps the identity to the identity, up to canonical isomorphism. -/
noncomputable def mapIdIso : Ind.map (𝟭 C) ≅ 𝟭 (Ind C) :=
  Functor.fullyFaithfulCancelRight (Ind.inclusion C)
    (mapCompInclusionIso (𝟭 C) ≪≫
      isoWhiskerLeft (Ind.inclusion C) lanIdIso ≪≫
      Functor.rightUnitor (Ind.inclusion C) ≪≫
      (Functor.leftUnitor (Ind.inclusion C)).symm)

variable {E : Type u} [SmallCategory E]

/-- Precomposition along a composite agrees with successive precomposition. -/
noncomputable def precomposeCompIso (F : C ⥤ D) (G : D ⥤ E) :
    (whiskeringLeft Cᵒᵖ Eᵒᵖ (Type u)).obj (F ⋙ G).op ≅
      (whiskeringLeft Dᵒᵖ Eᵒᵖ (Type u)).obj G.op ⋙
        (whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u)).obj F.op :=
  NatIso.ofComponents
    (fun X => isoWhiskerRight (Functor.opComp F G) X ≪≫
      Functor.associator F.op G.op X)
    (fun α => by
      ext X x
      exact ConcreteCategory.congr_hom
        (α.naturality ((Functor.opComp F G).hom.app X)).symm x)

/-- Successive presheaf left Kan extensions agree with extension along the composite. -/
noncomputable def lanCompIso (F : C ⥤ D) (G : D ⥤ E) :
    (F.op.lan : (Cᵒᵖ ⥤ Type u) ⥤ Dᵒᵖ ⥤ Type u) ⋙
        (G.op.lan : (Dᵒᵖ ⥤ Type u) ⥤ Eᵒᵖ ⥤ Type u) ≅
      ((F ⋙ G).op.lan : (Cᵒᵖ ⥤ Type u) ⥤ Eᵒᵖ ⥤ Type u) :=
  (((F.op.lanAdjunction (Type u)).comp (G.op.lanAdjunction (Type u))).ofNatIsoRight
    (precomposeCompIso F G).symm).leftAdjointUniq
      ((F ⋙ G).op.lanAdjunction (Type u))

/-- Covariant ind-extension respects composition, up to canonical isomorphism. -/
noncomputable def mapCompIso (F : C ⥤ D) (G : D ⥤ E) :
    Ind.map F ⋙ Ind.map G ≅ Ind.map (F ⋙ G) :=
  Functor.fullyFaithfulCancelRight (Ind.inclusion E)
    (Functor.associator (Ind.map F) (Ind.map G) (Ind.inclusion E) ≪≫
      isoWhiskerLeft (Ind.map F) (mapCompInclusionIso G) ≪≫
      (Functor.associator (Ind.map F) (Ind.inclusion D) G.op.lan).symm ≪≫
      isoWhiskerRight (mapCompInclusionIso F) G.op.lan ≪≫
      Functor.associator (Ind.inclusion C) F.op.lan G.op.lan ≪≫
      isoWhiskerLeft (Ind.inclusion C) (lanCompIso F G) ≪≫
      (mapCompInclusionIso (F ⋙ G)).symm)

end Ind

end CategoryTheory
