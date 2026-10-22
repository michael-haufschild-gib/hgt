import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysRationalWittPresheaf
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Stalks of the rational Witt structure sheaf

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Definitions 2.4 and 2.5.

The stalk of the sheaf `W_rat (𝒪_X)` is the stalk of the presheaf `U ↦ W_rat (𝒪_X (U))`, because
sheafification does not change stalks.  That stalk maps canonically to `W_rat (𝒪_{X,x})`, and
composing with `W_rat` of the residue map gives the map `W_rat (𝒪_{X,x}) → W_rat (κ (x))` appearing
in Deninger's locality condition.
-/

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat

universe u

variable {X : TopCat.{u}}

/-- Sheafification does not change the stalks of the rational Witt presheaf. -/
instance deningerRationalWittSheafify_stalk_isIso (F : TopCat.Presheaf CommRingCat.{u} X)
    (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (deningerRationalWittPresheaf F))) :=
  TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x CommRingCat.{u}
    (deningerRationalWittPresheaf F)

/-- The canonical comparison from the stalk of the rational Witt presheaf to the rational Witt ring
of the stalk. -/
noncomputable def deningerWittStalkToStalk (F : TopCat.Presheaf CommRingCat.{u} X) (x : X) :
    (deningerRationalWittPresheaf F).stalk x ⟶ deningerRationalWittFunctor.obj (F.stalk x) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ deningerRationalWittPresheaf F)
    { pt := deningerRationalWittFunctor.obj (F.stalk x)
      ι :=
        { app := fun (U : (OpenNhds x)ᵒᵖ) =>
            deningerRationalWittFunctor.map (F.germ (unop U).1 x (unop U).2)
          naturality := by
            intro U V f
            simp only [Functor.comp_map]
            show deningerRationalWittFunctor.map (F.map ((OpenNhds.inclusion x).op.map f)) ≫
                deningerRationalWittFunctor.map (F.germ (unop V).1 x (unop V).2)
              = deningerRationalWittFunctor.map (F.germ (unop U).1 x (unop U).2)
            rw [← Functor.map_comp]
            congr 1
            exact F.germ_res f.unop x (unop V).2 } }

@[simp] theorem deningerWittStalkToStalk_germ (F : TopCat.Presheaf CommRingCat.{u} X) (x : X)
    (U : Opens X) (hx : x ∈ U) :
    (deningerRationalWittPresheaf F).germ U x hx ≫ deningerWittStalkToStalk F x
      = deningerRationalWittFunctor.map (F.germ U x hx) :=
  Limits.colimit.ι_desc _ (op (⟨U, hx⟩ : OpenNhds x))

end RHTower


namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat AlgebraicGeometry

/-- The stalk of the rational Witt sheaf of a scheme compares with the rational Witt ring of the
stalk; sheafification does not change stalks. -/
noncomputable def deningerWittSheafStalkToStalk (X : Scheme.{u}) (x : X) :
    TopCat.Presheaf.stalk (X := X) (deningerRationalWittSheaf X.sheaf).1 x ⟶
      deningerRationalWittFunctor.obj (X.presheaf.stalk x) :=
  @inv _ _ _ _ ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (deningerRationalWittPresheaf X.presheaf)))
      (deningerRationalWittSheafify_stalk_isIso X.presheaf x)
    ≫ deningerWittStalkToStalk X.presheaf x

/-- **Deninger, Definition 2.3 (`t24n`).**  A morphism `W_rat (Y) → W_rat (X)` of rational Witt
spaces: a morphism of ringed spaces whose stalk maps `W_rat (𝒪_{X , f (y)}) → W_rat (𝒪_{Y,y})` are
compatible with the sheaf morphism and descend to the residue fields. -/
structure DeningerWittSpaceMorphism (Y X : Scheme.{u}) where
  /-- The underlying continuous map. -/
  base : (Y : TopCat.{u}) ⟶ (X : TopCat.{u})
  /-- The morphism of rational Witt structure sheaves. -/
  sheafMap : (deningerRationalWittSheaf X.sheaf).1 ⟶
    base _* (deningerRationalWittSheaf Y.sheaf).1
  /-- Deninger's map `f^♯_y` on stalks. -/
  stalkHom : ∀ y : Y, deningerRationalWittFunctor.obj (X.presheaf.stalk (base y)) ⟶
    deningerRationalWittFunctor.obj (Y.presheaf.stalk y)
  /-- It induces the stalk map of the morphism of sheaves. -/
  stalkHom_comp : ∀ y : Y,
    deningerWittStalkToStalk X.presheaf (base y) ≫ stalkHom y
      = (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (base y)).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
            (deningerRationalWittPresheaf X.presheaf) ≫ sheafMap) ≫
        TopCat.Presheaf.stalkPushforward CommRingCat.{u} base
          (deningerRationalWittSheaf Y.sheaf).1 y ≫
        deningerWittSheafStalkToStalk Y y
  /-- Deninger's locality condition. -/
  local' : ∀ y : Y, ∃ g : deningerRationalWittFunctor.obj (X.residueField (base y)) ⟶
      deningerRationalWittFunctor.obj (Y.residueField y),
    stalkHom y ≫ deningerRationalWittFunctor.map (Y.residue y)
      = deningerRationalWittFunctor.map (X.residue (base y)) ≫ g

/-- **Deninger, Definition 2.5 (`t25n`).**  A morphism `S → W_rat (X)`: a morphism of ringed spaces
whose stalk maps `W_rat (𝒪_{X , f (s)}) → 𝒪_{S,s}` are compatible with the sheaf morphism and are
*local*, i.e. descend to homomorphisms `W_rat (κ (f (s))) → κ (s)` on the residue data. -/
structure DeningerWittScheme (S X : Scheme.{u}) where
  /-- The underlying continuous map. -/
  base : (S : TopCat.{u}) ⟶ (X : TopCat.{u})
  /-- The morphism of structure sheaves. -/
  sheafMap : (deningerRationalWittSheaf X.sheaf).1 ⟶ base _* S.presheaf
  /-- Deninger's map `f^♯_s` on stalks. -/
  stalkHom : ∀ s : S, deningerRationalWittFunctor.obj (X.presheaf.stalk (base s)) ⟶
    S.presheaf.stalk s
  /-- It induces the stalk map of the morphism of sheaves. -/
  stalkHom_comp : ∀ s : S,
    deningerWittStalkToStalk X.presheaf (base s) ≫ stalkHom s
      = (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (base s)).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
            (deningerRationalWittPresheaf X.presheaf) ≫ sheafMap) ≫
        TopCat.Presheaf.stalkPushforward CommRingCat.{u} base S.presheaf s
  /-- Deninger's locality condition. -/
  local' : ∀ s : S, ∃ g : deningerRationalWittFunctor.obj (X.residueField (base s)) ⟶
      S.residueField s,
    stalkHom s ≫ S.residue s
      = deningerRationalWittFunctor.map (X.residue (base s)) ≫ g

end RHTower
