import GaloisForLFunctions.HTGeometry.SchemeOrderPullbackLaw

/-!
# The order pullback law along a morphism of schemes

A morphism of irreducible schemes carrying the generic point to the generic point induces a
homomorphism of function fields, and that homomorphism is compatible with the homomorphisms of
local rings it induces at every point.  The abstract pullback law for orders of vanishing
therefore applies to a genuine morphism: the order of the pullback of a rational function along a
codimension-one point is its ramification index times the order downstairs.
-/

namespace GaloisForLFunctions.HTGeometry

open AlgebraicGeometry CategoryTheory Order IsDiscreteValuationRing

universe u

/-- The homomorphism of function fields induced by a morphism carrying the generic point to the
generic point. -/
noncomputable def functionFieldMap {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) (hf : f.base (genericPoint X) = genericPoint Y) :
    Y.functionField →+* X.functionField :=
  (Y.presheaf.stalkSpecializes (specializes_of_eq hf) ≫ f.stalkMap (genericPoint X)).hom

/-- **The induced map of function fields extends the induced maps of local rings.** -/
theorem functionFieldMap_algebraMap {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) (hf : f.base (genericPoint X) = genericPoint Y) (z : X)
    (s : Y.presheaf.stalk (f.base z)) :
    functionFieldMap f hf (algebraMap (Y.presheaf.stalk (f.base z)) Y.functionField s) =
      algebraMap (X.presheaf.stalk z) X.functionField (f.stalkMap z s) := by
  have hgen : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
  simp only [functionFieldMap, RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp,
    RingHom.coe_comp, Function.comp_apply, TopCat.Presheaf.stalkSpecializes_comp_apply]
  exact Scheme.Hom.stalkSpecializes_stalkMap_apply f (genericPoint X) z hgen s

/-- **The order of vanishing of a pullback along a morphism of schemes.**  At codimension-one
points whose local rings are discrete valuation rings, the order of the pullback is the
ramification index of the induced map of local rings times the order downstairs. -/
theorem ord_functionFieldMap_eq_mul_ramification
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (hf : f.base (genericPoint X) = genericPoint Y)
    {z : X} (hz : coheight z = 1) (hw : coheight (f.base z) = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk z)]
    [IsDiscreteValuationRing (Y.presheaf.stalk (f.base z))]
    {π : Y.presheaf.stalk (f.base z)} (hπ : Irreducible π) (e : ℕ)
    (he : addVal (X.presheaf.stalk z) ((f.stalkMap z).hom π) = (e : ℕ∞))
    {g : Y.functionField} (hg : g ≠ 0) :
    Scheme.ord (functionFieldMap f hf g) z = (e : ℤ) * Scheme.ord g (f.base z) :=
  ord_pullback_eq_mul_ramification hz hw (f.stalkMap z).hom (functionFieldMap f hf)
    (functionFieldMap_algebraMap f hf z) hπ e he hg

end GaloisForLFunctions.HTGeometry
