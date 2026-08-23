import GaloisForLFunctions.RHTower.DeningerDynSysTwoPointGamma
import GaloisForLFunctions.RHTower.DeningerDynSysWittSheafSections

/-!
# The sheaf morphism of Proposition 13.1

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 13.1.

The presheaf morphism attached to the two stalk maps extends to the sheafification by its
universal property, because the direct image of a sheaf is a sheaf.
-/

namespace RHTower

open CategoryTheory Opposite TopologicalSpace TopCat AlgebraicGeometry

noncomputable section

universe u

variable {X S : TopCat.{u}} (Fsh : TopCat.Sheaf CommRingCat.{u} X)
  (Gsh : TopCat.Sheaf CommRingCat.{u} S) (base : S ⟶ X)
variable {x y : X} (hspec : x ⤳ y) (Vgen : Opens S)
variable (hgen : ∀ U : Opens X, y ∉ U → (Opens.map base).obj U ≤ Vgen)
variable (hbot : ∀ U : Opens X, x ∉ U → (Opens.map base).obj U = ⊥)
variable (hterm : Limits.IsTerminal (Gsh.1.obj (op (⊥ : Opens S))))
variable (fs : deningerRationalWittFunctor.obj (TopCat.Presheaf.stalk Fsh.1 y) ⟶
  Gsh.1.obj (op ⊤))
variable (fgen : deningerRationalWittFunctor.obj (TopCat.Presheaf.stalk Fsh.1 x) ⟶
  Gsh.1.obj (op Vgen))
variable (hsq : deningerRationalWittFunctor.map
    (TopCat.Presheaf.stalkSpecializes Fsh.1 hspec) ≫ fgen
  = fs ≫ Gsh.1.map (homOfLE (le_top : Vgen ≤ ⊤)).op)

include hspec hsq in
/-- **Deninger, Proposition 13.1, diagram (139).**  The morphism of sheaves
`W_rat (𝒪_X) ⟶ f_* 𝒪_S` attached to the two stalk maps. -/
def deningerTwoPointSheafMap : (deningerRationalWittSheaf Fsh).1 ⟶ base _* Gsh.1 :=
  CategoryTheory.sheafifyLift (Opens.grothendieckTopology X)
    (deningerTwoPointGamma Fsh.1 Gsh.1 base hspec Vgen hgen hbot hterm fs fgen hsq)
    (TopCat.Sheaf.pushforward_sheaf_of_sheaf base Gsh.2)

include hspec hsq in
/-- The sheaf morphism restricts to the presheaf morphism along the unit of the
sheafification. -/
theorem deningerTwoPointSheafMap_comp_unit :
    deningerRationalWittUnit Fsh ≫
        deningerTwoPointSheafMap Fsh Gsh base hspec Vgen hgen hbot hterm fs fgen hsq
      = deningerTwoPointGamma Fsh.1 Gsh.1 base hspec Vgen hgen hbot hterm fs fgen hsq :=
  CategoryTheory.toSheafify_sheafifyLift _ _ _

end

end RHTower
