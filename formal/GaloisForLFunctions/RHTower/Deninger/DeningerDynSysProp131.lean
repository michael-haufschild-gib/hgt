import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysTwoPointStalks
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysTwoPointSheafMap
import GaloisForLFunctions.HTGeometry.SpecTwoPointBase

/-!
# Proposition 13.1: the `𝒪`-valued point of `W_rat (X)`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 13.1.

A pair of stalk maps `f_s`, `f_η` satisfying the commuting square (139), together with the
locality data (140), assembles into a morphism `Spec 𝒪 → W_rat (X)` in the sense of Definition
2.5.  Since the rational Witt construction commutes with stalks, the stalk maps of that morphism
are prescribed by the sheaf morphism, so the two remaining fields of Definition 2.5 carry no
information; and the stalk computations recover `f_s` and `f_η`.
-/

namespace RHTower

open CategoryTheory Opposite TopologicalSpace TopCat AlgebraicGeometry HTGeometry
open IsLocalRing

noncomputable section

universe u

variable {X : Scheme.{u}} (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R]
variable (hdim : ∀ P : Ideal R, P.IsPrime → P = ⊥ ∨ P = maximalIdeal R) (hfield : ¬ IsField R)
variable (base : ((Spec R : Scheme.{u}) : TopCat.{u}) ⟶ ((X : Scheme.{u}) : TopCat.{u}))
variable (hspec : base (specGeneric (R : Type u)) ⤳ base (specClosed (R : Type u)))
variable (hgen : ∀ U : X.Opens, base (specClosed (R : Type u)) ∉ U →
  (Opens.map base).obj U ≤ specGenericOpen R hdim hfield)
variable (hbot : ∀ U : X.Opens, base (specGeneric (R : Type u)) ∉ U →
  (Opens.map base).obj U = ⊥)
variable
  (fs : deningerRationalWittFunctor.obj
      (TopCat.Presheaf.stalk X.presheaf (base (specClosed (R : Type u)))) ⟶
    (Spec R).presheaf.obj (op ⊤))
  (fgen : deningerRationalWittFunctor.obj
      (TopCat.Presheaf.stalk X.presheaf (base (specGeneric (R : Type u)))) ⟶
    (Spec R).presheaf.obj (op (specGenericOpen R hdim hfield)))
variable (hsq : deningerRationalWittFunctor.map
      (TopCat.Presheaf.stalkSpecializes X.presheaf hspec) ≫ fgen
    = fs ≫ (Spec R).presheaf.map
      (homOfLE (le_top : specGenericOpen R hdim hfield ≤ ⊤)).op)

/-- **Deninger, Proposition 13.1.**  The sheaf morphism attached to the pair of stalk maps. -/
def deningerProp131SheafMap :
    (deningerRationalWittSheaf X.sheaf).1 ⟶ base _* (Spec R).presheaf :=
  deningerTwoPointSheafMap X.sheaf (Spec R).sheaf base hspec (specGenericOpen R hdim hfield)
    hgen hbot (Spec R).sheaf.isTerminalOfEmpty fs fgen hsq

set_option backward.isDefEq.respectTransparency false in
theorem deningerProp131SheafMap_unit :
    CategoryTheory.toSheafify (Opens.grothendieckTopology (X : TopCat.{u}))
          (deningerRationalWittPresheaf X.presheaf) ≫
        deningerProp131SheafMap R hdim hfield base hspec hgen hbot fs fgen hsq
      = deningerTwoPointGamma X.presheaf (Spec R).presheaf base hspec
        (specGenericOpen R hdim hfield) hgen hbot (Spec R).sheaf.isTerminalOfEmpty fs fgen hsq :=
  deningerTwoPointSheafMap_comp_unit X.sheaf (Spec R).sheaf base hspec _ hgen hbot _ fs fgen hsq

/-- The stalk map prescribed by a morphism of rational Witt sheaves. -/
def deningerProp131StalkHom (p : (Spec R : Scheme.{u})) :
    deningerRationalWittFunctor.obj (TopCat.Presheaf.stalk X.presheaf (base p)) ⟶
      TopCat.Presheaf.stalk (Spec R).presheaf p :=
  inv (deningerWittStalkToStalk X.presheaf (base p)) ≫
    (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (base p)).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology (X : TopCat.{u}))
        (deningerRationalWittPresheaf X.presheaf) ≫
        deningerProp131SheafMap R hdim hfield base hspec hgen hbot fs fgen hsq) ≫
    TopCat.Presheaf.stalkPushforward CommRingCat.{u} base (Spec R).presheaf p

set_option backward.isDefEq.respectTransparency false in
/-- The stalk map is compatible with the sheaf morphism, by construction. -/
theorem deningerProp131StalkHom_comp (p : (Spec R : Scheme.{u})) :
    deningerWittStalkToStalk X.presheaf (base p) ≫
        deningerProp131StalkHom R hdim hfield base hspec hgen hbot fs fgen hsq p
      = (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (base p)).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology (X : TopCat.{u}))
            (deningerRationalWittPresheaf X.presheaf) ≫
            deningerProp131SheafMap R hdim hfield base hspec hgen hbot fs fgen hsq) ≫
        TopCat.Presheaf.stalkPushforward CommRingCat.{u} base (Spec R).presheaf p := by
  rw [deningerProp131StalkHom, IsIso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- **Deninger, Proposition 13.1.**  At the closed point the stalk map is `f_s`. -/
theorem deningerProp131StalkHom_closed :
    deningerProp131StalkHom R hdim hfield base hspec hgen hbot fs fgen hsq
        (specClosed (R : Type u))
      = fs ≫ TopCat.Presheaf.germ (Spec R).presheaf ⊤ (specClosed (R : Type u)) trivial := by
  rw [deningerProp131StalkHom, deningerProp131SheafMap_unit,
    deningerTwoPointGamma_stalk_closed X.presheaf (Spec R).presheaf base
      (specGeneric (R : Type u)) (specClosed (R : Type u)) hspec _ hgen hbot _ fs fgen hsq,
    IsIso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- **Deninger, Proposition 13.1.**  At the generic point the stalk map is `f_η`. -/
theorem deningerProp131StalkHom_generic :
    deningerProp131StalkHom R hdim hfield base hspec hgen hbot fs fgen hsq
        (specGeneric (R : Type u))
      = fgen ≫ TopCat.Presheaf.germ (Spec R).presheaf (specGenericOpen R hdim hfield)
        (specGeneric (R : Type u)) (mem_specGenericOpen R hdim hfield) := by
  rw [deningerProp131StalkHom, deningerProp131SheafMap_unit,
    deningerTwoPointGamma_stalk_generic X.presheaf (Spec R).presheaf base
      (specGeneric (R : Type u)) (specClosed (R : Type u)) hspec _ hgen hbot _ fs fgen hsq
      (mem_specGenericOpen R hdim hfield),
    IsIso.inv_hom_id_assoc]

variable
  (hlocs : ∃ g : deningerRationalWittFunctor.obj
      (X.residueField (base (specClosed (R : Type u)))) ⟶
        (Spec R).residueField (specClosed (R : Type u)),
    (fs ≫ TopCat.Presheaf.germ (Spec R).presheaf ⊤ (specClosed (R : Type u)) trivial) ≫
        (Spec R).residue (specClosed (R : Type u))
      = deningerRationalWittFunctor.map (X.residue (base (specClosed (R : Type u)))) ≫ g)
  (hlocgen : ∃ g : deningerRationalWittFunctor.obj
      (X.residueField (base (specGeneric (R : Type u)))) ⟶
        (Spec R).residueField (specGeneric (R : Type u)),
    (fgen ≫ TopCat.Presheaf.germ (Spec R).presheaf (specGenericOpen R hdim hfield)
          (specGeneric (R : Type u)) (mem_specGenericOpen R hdim hfield)) ≫
        (Spec R).residue (specGeneric (R : Type u))
      = deningerRationalWittFunctor.map (X.residue (base (specGeneric (R : Type u)))) ≫ g)

set_option backward.isDefEq.respectTransparency false in
/-- **Deninger, Proposition 13.1.**  A pair of stalk maps satisfying the square (139) and the
locality data (140) is a morphism `Spec 𝒪 → W_rat (X)` in the sense of Definition 2.5. -/
def deningerProp131WittScheme : DeningerWittScheme (Spec R) X where
  base := base
  sheafMap := deningerProp131SheafMap R hdim hfield base hspec hgen hbot fs fgen hsq
  stalkHom := deningerProp131StalkHom R hdim hfield base hspec hgen hbot fs fgen hsq
  stalkHom_comp := deningerProp131StalkHom_comp R hdim hfield base hspec hgen hbot fs fgen hsq
  local' := by
    intro p
    rcases spec_eq_generic_or_closed hdim p with h | h
    · subst h
      obtain ⟨g, hg⟩ := hlocgen
      refine ⟨g, ?_⟩
      rw [deningerProp131StalkHom_generic, Category.assoc] at *
      exact hg
    · subst h
      obtain ⟨g, hg⟩ := hlocs
      refine ⟨g, ?_⟩
      rw [deningerProp131StalkHom_closed, Category.assoc] at *
      exact hg

end

end RHTower
