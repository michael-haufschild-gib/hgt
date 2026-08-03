import GaloisForLFunctions.HTGeometry.FunctionFieldPullback

/-!
# From represented scheme functors to function fields

This file is the bridge from functor-of-points constructions to rational function fields.  It uses
mathlib's categorical `RepresentableBy`, so representing objects are schemes, not chosen point-set
models.  Two representations yield a canonical scheme isomorphism and hence a contravariant
isomorphism of their function fields.  Natural transformations between represented functors yield
the actual representing scheme morphism via full faithfulness of Yoneda.
-/

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- A set-valued functor on schemes, in the variance used by functors of points. -/
abbrev SchemeSetFunctor := Scheme.{u}ᵒᵖ ⥤ Type u

/-- Representing schemes for the same scheme functor are canonically isomorphic. -/
noncomputable def representingSchemeIso {F : SchemeSetFunctor} {X Y : Scheme.{u}}
    (hX : F.RepresentableBy X) (hY : F.RepresentableBy Y) : X ≅ Y :=
  hX.uniqueUpToIso hY

/-- The canonical isomorphism between two integral representing schemes induces the canonical
contravariant equivalence of their function fields. -/
noncomputable def representingFunctionFieldEquiv
    {F : SchemeSetFunctor} {X Y : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y]
    (hX : F.RepresentableBy X) (hY : F.RepresentableBy Y) :
    Y.functionField ≃+* X.functionField :=
  Scheme.Iso.functionFieldPullbackRingEquiv (representingSchemeIso hX hY)

/-- A natural transformation between represented scheme functors is represented by an actual
scheme morphism. -/
noncomputable def representedMorphism
    {F G : SchemeSetFunctor} {X Y : Scheme.{u}}
    (hX : F.RepresentableBy X) (hY : G.RepresentableBy Y) (eta : F ⟶ G) : X ⟶ Y :=
  Yoneda.fullyFaithful.preimage (hX.toIso.hom ≫ eta ≫ hY.toIso.inv)

/-- Yoneda sends the represented morphism back to the original natural transformation, expressed
in the chosen representations. -/
theorem yoneda_map_representedMorphism
    {F G : SchemeSetFunctor} {X Y : Scheme.{u}}
    (hX : F.RepresentableBy X) (hY : G.RepresentableBy Y) (eta : F ⟶ G) :
    yoneda.map (representedMorphism hX hY eta) = hX.toIso.hom ≫ eta ≫ hY.toIso.inv :=
  Yoneda.fullyFaithful.map_preimage _

/-- A dominant represented natural transformation induces the expected injective pullback on
function fields. -/
noncomputable def representedFunctionFieldPullback
    {F G : SchemeSetFunctor} {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y]
    (hX : F.RepresentableBy X) (hY : G.RepresentableBy Y) (eta : F ⟶ G)
    [IsDominant (representedMorphism hX hY eta)] :
    Y.functionField ⟶ X.functionField :=
  (representedMorphism hX hY eta).functionFieldPullback

theorem representedFunctionFieldPullback_injective
    {F G : SchemeSetFunctor} {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y]
    (hX : F.RepresentableBy X) (hY : G.RepresentableBy Y) (eta : F ⟶ G)
    [IsDominant (representedMorphism hX hY eta)] :
    Function.Injective (representedFunctionFieldPullback hX hY eta) :=
  Scheme.Hom.functionFieldPullback_injective (representedMorphism hX hY eta)

end AlgebraicGeometry
