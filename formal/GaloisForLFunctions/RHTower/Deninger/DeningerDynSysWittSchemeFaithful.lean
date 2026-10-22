import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysWittFaithful
import GaloisForLFunctions.HTGeometry.SchemeHomStalkExt

/-!
# Faithfulness of the rational Witt construction on morphisms of schemes

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 2.4
(`t27xn`), at the level of schemes.

Two morphisms of schemes with the same underlying continuous map whose rational Witt stalk maps
agree on Teichmüller germs are equal: the Teichmüller map is injective, so the stalk maps
themselves agree, and a morphism of schemes is determined by its underlying map together with its
stalk maps.
-/

namespace RHTower

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

/-- The Teichmüller map is natural for the rational Witt functor on `CommRingCat`. -/
theorem deningerRationalWittFunctor_map_teichmuller {A B : CommRingCat.{u}} (φ : A ⟶ B) (a : A) :
    deningerRationalWittFunctor.map φ (deningerCanonicalRationalWittTeichmuller a)
      = deningerCanonicalRationalWittTeichmuller (φ a) :=
  deningerCanonicalRationalWittMap_teichmuller φ.hom a

/-- **Deninger, Proposition 2.4 (`t27xn`).**  A morphism of schemes is determined by its
underlying continuous map together with the induced maps of rational Witt rings on stalks; that
is, the rational Witt construction is faithful on morphisms of schemes. -/
theorem deningerWitt_scheme_hom_ext {X Y : Scheme.{u}} {α β : Y ⟶ X}
    (h_base : α.base = β.base)
    (h_stalk : ∀ (y : Y) (U : X.Opens) (hα : α.base y ∈ U) (hβ : β.base y ∈ U)
      (s : X.presheaf.obj (op U)),
      deningerRationalWittFunctor.map (α.stalkMap y)
          (deningerCanonicalRationalWittTeichmuller (X.presheaf.germ U (α.base y) hα s))
        = deningerRationalWittFunctor.map (β.stalkMap y)
          (deningerCanonicalRationalWittTeichmuller (X.presheaf.germ U (β.base y) hβ s))) :
    α = β := by
  refine HTGeometry.scheme_hom_ext_of_stalkMap h_base fun y U hα hβ s => ?_
  refine deningerCanonicalRationalWittTeichmuller_injective ?_
  have h := h_stalk y U hα hβ s
  rwa [deningerRationalWittFunctor_map_teichmuller,
    deningerRationalWittFunctor_map_teichmuller] at h

end RHTower
