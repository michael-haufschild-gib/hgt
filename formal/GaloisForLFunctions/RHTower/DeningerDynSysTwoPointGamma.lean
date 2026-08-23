import GaloisForLFunctions.RHTower.DeningerDynSysRationalWittPresheaf

/-!
# The sheaf morphism attached to a pair of stalk maps over a two-point base

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 13.1,
diagram (139).

Let `f : S → X` be a continuous map whose image is a specialisation `x ⤳ y`, so that the preimage
of an open set of `X` is the whole of `S` if it contains `y`, is contained in a fixed open `V` if
it does not contain `y`, and is empty if it does not contain `x`.  A homomorphism `f_s` on
`W_rat (𝒪_{X,y})` with values in `Γ (S , ⊤)` and a homomorphism `f_η` on `W_rat (𝒪_{X,x})` with
values in `Γ (S , V)` which agree after restriction assemble into a morphism of presheaves
`W_rat (𝒪_X) ⟶ f_* 𝒪_S`.
-/

namespace RHTower

open CategoryTheory Opposite TopologicalSpace TopCat AlgebraicGeometry

noncomputable section

universe u

variable {X S : TopCat.{u}} (F : TopCat.Presheaf CommRingCat.{u} X)
  (G : TopCat.Presheaf CommRingCat.{u} S) (base : S ⟶ X)
variable {x y : X} (hspec : x ⤳ y) (Vgen : Opens S)
variable (hgen : ∀ U : Opens X, y ∉ U → (Opens.map base).obj U ≤ Vgen)
variable (hbot : ∀ U : Opens X, x ∉ U → (Opens.map base).obj U = ⊥)
variable (hterm : Limits.IsTerminal (G.obj (op (⊥ : Opens S))))
variable (fs : deningerRationalWittFunctor.obj (F.stalk y) ⟶ G.obj (op ⊤))
variable (fgen : deningerRationalWittFunctor.obj (F.stalk x) ⟶ G.obj (op Vgen))

open scoped Classical in
/-- **Deninger, Proposition 13.1, diagram (139).**  The component of the sheaf morphism over an
open set of `X`. -/
def deningerTwoPointGammaApp (U : Opens X) :
    (deningerRationalWittPresheaf F).obj (op U) ⟶ (base _* G).obj (op U) :=
  if hy : y ∈ U then
    deningerRationalWittFunctor.map (F.germ U y hy) ≫ fs ≫ G.map (homOfLE le_top).op
  else if hx : x ∈ U then
    deningerRationalWittFunctor.map (F.germ U x hx) ≫ fgen ≫ G.map (homOfLE (hgen U hy)).op
  else
    (hterm.from _) ≫ G.map (homOfLE (le_of_eq (hbot U hx))).op

variable (hsq : deningerRationalWittFunctor.map (F.stalkSpecializes hspec) ≫ fgen
  = fs ≫ G.map (homOfLE (le_top : Vgen ≤ ⊤)).op)

set_option backward.isDefEq.respectTransparency false in
include hspec hgen hbot hsq in
/-- **Deninger, Proposition 13.1, diagram (139).**  Naturality of the components. -/
theorem deningerTwoPointGamma_naturality (U V : Opens X) (hUV : U ≤ V) :
    (deningerRationalWittPresheaf F).map (homOfLE hUV).op ≫
        deningerTwoPointGammaApp F G base Vgen hgen hbot hterm fs fgen U
      = deningerTwoPointGammaApp F G base Vgen hgen hbot hterm fs fgen V ≫
        (base _* G).map (homOfLE hUV).op := by
  classical
  by_cases hxU : x ∈ U
  · have hxV : x ∈ V := hUV hxU
    by_cases hyU : y ∈ U
    · have hyV : y ∈ V := hUV hyU
      rw [deningerTwoPointGammaApp, dif_pos hyU, deningerTwoPointGammaApp, dif_pos hyV]
      show deningerRationalWittFunctor.map (F.map (homOfLE hUV).op) ≫ _ = _
      simp only [Category.assoc, TopCat.Presheaf.pushforward_obj_map, ← Functor.map_comp_assoc,
        TopCat.Presheaf.germ_res]
      congr 2
      rw [← Functor.map_comp]
      exact congrArg _ (Subsingleton.elim _ _)
    · rw [deningerTwoPointGammaApp, dif_neg hyU, dif_pos hxU]
      by_cases hyV : y ∈ V
      · rw [deningerTwoPointGammaApp, dif_pos hyV]
        show deningerRationalWittFunctor.map (F.map (homOfLE hUV).op) ≫ _ = _
        simp only [Category.assoc, TopCat.Presheaf.pushforward_obj_map, ← Functor.map_comp_assoc,
          TopCat.Presheaf.germ_res]
        rw [← TopCat.Presheaf.germ_stalkSpecializes F hyV hspec, Functor.map_comp,
          Category.assoc, reassoc_of% hsq]
        simp only [← Functor.map_comp]
        congr 2
      · rw [deningerTwoPointGammaApp, dif_neg hyV, dif_pos hxV]
        show deningerRationalWittFunctor.map (F.map (homOfLE hUV).op) ≫ _ = _
        simp only [Category.assoc, TopCat.Presheaf.pushforward_obj_map, ← Functor.map_comp_assoc,
          TopCat.Presheaf.germ_res]
        congr 2
        rw [← Functor.map_comp]
        exact congrArg _ (Subsingleton.elim _ _)
  · haveI : Subsingleton (((base _* G).obj (op U)) : Type u) := by
      show Subsingleton ((G.obj (op ((Opens.map base).obj U))) : Type u)
      rw [hbot U hxU]
      exact CommRingCat.subsingleton_of_isTerminal hterm
    exact CommRingCat.hom_ext (RingHom.ext fun a => Subsingleton.elim _ _)

include hspec hsq in
/-- **Deninger, Proposition 13.1, diagram (139).**  The morphism of presheaves
`W_rat (𝒪_X) ⟶ f_* 𝒪_S` attached to the two stalk maps. -/
def deningerTwoPointGamma : deningerRationalWittPresheaf F ⟶ base _* G where
  app U := deningerTwoPointGammaApp F G base Vgen hgen hbot hterm fs fgen U.unop
  naturality U V i := by
    rw [Subsingleton.elim i (homOfLE i.unop.le).op]
    exact deningerTwoPointGamma_naturality F G base hspec Vgen hgen hbot hterm fs fgen hsq
      V.unop U.unop i.unop.le

@[simp] theorem deningerTwoPointGamma_app (U : Opens X) :
    (deningerTwoPointGamma F G base hspec Vgen hgen hbot hterm fs fgen hsq).app (op U)
      = deningerTwoPointGammaApp F G base Vgen hgen hbot hterm fs fgen U := rfl

end

end RHTower
