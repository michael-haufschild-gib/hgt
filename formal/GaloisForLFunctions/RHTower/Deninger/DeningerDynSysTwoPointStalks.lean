import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysTwoPointGamma
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysWittStalkIso

/-!
# The two stalk maps of the morphism of Proposition 13.1

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 13.1.

The stalk of the morphism `γ : W_rat (𝒪_X) ⟶ f_* 𝒪_S` at the closed point of `S` is `f_s`
followed by the germ over the whole space, and at the generic point it is `f_η` followed by the
germ over `V`.  Both are checked on germs, the generic case using Deninger's square (139).
-/

namespace RHTower

open CategoryTheory Opposite TopologicalSpace TopCat AlgebraicGeometry

noncomputable section

universe u

variable {X S : TopCat.{u}} (F : TopCat.Presheaf CommRingCat.{u} X)
  (G : TopCat.Presheaf CommRingCat.{u} S) (base : S ⟶ X)
variable (eta sig : S) (hspec : base eta ⤳ base sig) (Vgen : Opens S)
variable (hgen : ∀ U : Opens X, base sig ∉ U → (Opens.map base).obj U ≤ Vgen)
variable (hbot : ∀ U : Opens X, base eta ∉ U → (Opens.map base).obj U = ⊥)
variable (hterm : Limits.IsTerminal (G.obj (op (⊥ : Opens S))))
variable (fs : deningerRationalWittFunctor.obj (F.stalk (base sig)) ⟶ G.obj (op ⊤))
variable (fgen : deningerRationalWittFunctor.obj (F.stalk (base eta)) ⟶ G.obj (op Vgen))
variable (hsq : deningerRationalWittFunctor.map (F.stalkSpecializes hspec) ≫ fgen
  = fs ≫ G.map (homOfLE (le_top : Vgen ≤ ⊤)).op)

set_option backward.isDefEq.respectTransparency false in
include hspec hsq in
/-- **Deninger, Proposition 13.1.**  The stalk of `γ` at the closed point is `f_s`. -/
theorem deningerTwoPointGamma_stalk_closed :
    (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (base sig)).map
        (deningerTwoPointGamma F G base hspec Vgen hgen hbot hterm fs fgen hsq) ≫
      G.stalkPushforward CommRingCat.{u} base sig
      = deningerWittStalkToStalk F (base sig) ≫ fs ≫ G.germ ⊤ sig trivial := by
  classical
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc,
    TopCat.Presheaf.stalkPushforward_germ]
  rw [← Category.assoc, deningerWittStalkToStalk_germ]
  show deningerTwoPointGammaApp F G base Vgen hgen hbot hterm fs fgen U ≫ _ = _
  rw [deningerTwoPointGammaApp, dif_pos hU]
  simp only [Category.assoc]
  congr 2
  rw [TopCat.Presheaf.germ_res]

set_option backward.isDefEq.respectTransparency false in
include hspec hsq in
/-- **Deninger, Proposition 13.1.**  The stalk of `γ` at the generic point is `f_η`. -/
theorem deningerTwoPointGamma_stalk_generic (hetaV : eta ∈ Vgen) :
    (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (base eta)).map
        (deningerTwoPointGamma F G base hspec Vgen hgen hbot hterm fs fgen hsq) ≫
      G.stalkPushforward CommRingCat.{u} base eta
      = deningerWittStalkToStalk F (base eta) ≫ fgen ≫ G.germ Vgen eta hetaV := by
  classical
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc,
    TopCat.Presheaf.stalkPushforward_germ]
  rw [← Category.assoc, deningerWittStalkToStalk_germ]
  show deningerTwoPointGammaApp F G base Vgen hgen hbot hterm fs fgen U ≫ _ = _
  rw [deningerTwoPointGammaApp]
  by_cases hy : base sig ∈ U
  · rw [dif_pos hy]
    simp only [Category.assoc]
    rw [TopCat.Presheaf.germ_res, ← TopCat.Presheaf.germ_stalkSpecializes F hy hspec,
      Functor.map_comp, Category.assoc, reassoc_of% hsq]
    congr 2
    rw [TopCat.Presheaf.germ_res]
  · rw [dif_neg hy, dif_pos hU, Category.assoc, Category.assoc]
    congr 2
    rw [TopCat.Presheaf.germ_res]

end

end RHTower
