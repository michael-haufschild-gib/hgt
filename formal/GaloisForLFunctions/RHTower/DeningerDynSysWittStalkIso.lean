import GaloisForLFunctions.HTGeometry.GermPolynomialLift
import GaloisForLFunctions.RHTower.DeningerDynSysWittStalk
import GaloisForLFunctions.RHTower.DeningerRationalWittLocalization

/-!
# The rational Witt construction commutes with stalks

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Definition 2.5 and
Proposition 13.1.

A rational Witt vector is a normalised fraction of polynomials, so it is determined by finitely
many coefficients.  Hence the canonical comparison from the stalk of `U ↦ W_rat (𝒪 (U))` to
`W_rat (𝒪_x)` is bijective: surjective because the finitely many coefficients of a normalised
fraction over the stalk lift to a common neighbourhood, and injective because a normalised
fraction vanishes exactly when numerator and denominator agree, which is finitely many equalities
of germs.
-/

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat HTGeometry

universe u

variable {X : TopCat.{u}} (F : TopCat.Presheaf CommRingCat.{u} X) (x : X)

set_option backward.isDefEq.respectTransparency false in
/-- The comparison to the rational Witt ring of the stalk is surjective. -/
theorem deningerWittStalkToStalk_surjective :
    Function.Surjective (deningerWittStalkToStalk F x) := by
  intro α
  obtain ⟨P, Q, hP, hQ, hα⟩ := deningerCanonicalRationalWitt_eq_normalizedFraction α
  obtain ⟨U₁, hx₁, P₁, hP₁, hP₁map⟩ := exists_germ_lift_normalized_polynomial F x P hP
  obtain ⟨U₂, hx₂, Q₂, hQ₂, hQ₂map⟩ := exists_germ_lift_normalized_polynomial F x Q hQ
  set U : Opens X := U₁ ⊓ U₂ with hU
  have hxU : x ∈ U := ⟨hx₁, hx₂⟩
  set P' : Polynomial (F.obj (op U) : Type u) :=
    P₁.map (F.map (homOfLE (inf_le_left : U ≤ U₁)).op).hom with hP'
  set Q' : Polynomial (F.obj (op U) : Type u) :=
    Q₂.map (F.map (homOfLE (inf_le_right : U ≤ U₂)).op).hom with hQ'
  have hP'0 : P'.coeff 0 = 1 := by
    rw [hP', Polynomial.coeff_map, hP₁]
    exact map_one _
  have hQ'0 : Q'.coeff 0 = 1 := by
    rw [hQ', Polynomial.coeff_map, hQ₂]
    exact map_one _
  have hP'map : P'.map (F.germ U x hxU).hom = P := by
    rw [hP', Polynomial.map_map]
    rw [show (F.germ U x hxU).hom.comp (F.map (homOfLE (inf_le_left : U ≤ U₁)).op).hom
        = (F.map (homOfLE (inf_le_left : U ≤ U₁)).op ≫ F.germ U x hxU).hom from rfl]
    rw [TopCat.Presheaf.germ_res F (homOfLE (inf_le_left : U ≤ U₁)) x hxU]
    exact hP₁map
  have hQ'map : Q'.map (F.germ U x hxU).hom = Q := by
    rw [hQ', Polynomial.map_map]
    rw [show (F.germ U x hxU).hom.comp (F.map (homOfLE (inf_le_right : U ≤ U₂)).op).hom
        = (F.map (homOfLE (inf_le_right : U ≤ U₂)).op ≫ F.germ U x hxU).hom from rfl]
    rw [TopCat.Presheaf.germ_res F (homOfLE (inf_le_right : U ≤ U₂)) x hxU]
    exact hQ₂map
  refine ⟨(deningerRationalWittPresheaf F).germ U x hxU
    (deningerCanonicalRationalWittNormalizedFraction P' Q' hP'0 hQ'0), ?_⟩
  rw [← ConcreteCategory.comp_apply, deningerWittStalkToStalk_germ]
  show deningerCanonicalRationalWittMap (F.germ U x hxU).hom
      (deningerCanonicalRationalWittNormalizedFraction P' Q' hP'0 hQ'0) = α
  rw [deningerCanonicalRationalWittMap_normalizedFraction, hα]
  exact deningerCanonicalRationalWittNormalizedFraction_congr _ _ _ _ hP'map hQ'map

set_option backward.isDefEq.respectTransparency false in
/-- Sections whose rational Witt vectors have the same image in `W_rat (𝒪_x)` have the same
germ. -/
theorem deningerWittStalkToStalk_germ_inj (V : Opens X) (hxV : x ∈ V)
    (a b : ((deningerRationalWittPresheaf F).obj (op V) : Type u))
    (h : deningerCanonicalRationalWittMap (F.germ V x hxV).hom a
      = deningerCanonicalRationalWittMap (F.germ V x hxV).hom b) :
    (deningerRationalWittPresheaf F).germ V x hxV a
      = (deningerRationalWittPresheaf F).germ V x hxV b := by
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := deningerCanonicalRationalWitt_eq_normalizedFraction (a - b)
  have hzero : deningerCanonicalRationalWittMap (F.germ V x hxV).hom (a - b) = 0 := by
    rw [map_sub, h, sub_self]
  rw [hPQ, deningerCanonicalRationalWittMap_normalizedFraction] at hzero
  have hmap : P.map (F.germ V x hxV).hom = Q.map (F.germ V x hxV).hom :=
    (deningerCanonicalRationalWittNormalizedFraction_eq_zero_iff _ _ _ _).1 hzero
  obtain ⟨W, hxW, i, hi⟩ := exists_res_eq_of_germ_eq_polynomial F x V hxV P Q hmap
  have hres : deningerCanonicalRationalWittMap (F.map i.op).hom (a - b) = 0 := by
    rw [hPQ, deningerCanonicalRationalWittMap_normalizedFraction]
    exact (deningerCanonicalRationalWittNormalizedFraction_eq_zero_iff _ _ _ _).2 hi
  have hab : (deningerRationalWittPresheaf F).map i.op a
      = (deningerRationalWittPresheaf F).map i.op b := by
    have h1 : deningerCanonicalRationalWittMap (F.map i.op).hom a
        - deningerCanonicalRationalWittMap (F.map i.op).hom b = 0 := by
      rw [← map_sub]
      exact hres
    have h2 := sub_eq_zero.1 h1
    exact h2
  have hga : (deningerRationalWittPresheaf F).germ W x hxW
        ((deningerRationalWittPresheaf F).map i.op a)
      = (deningerRationalWittPresheaf F).germ V x hxV a :=
    TopCat.Presheaf.germ_res_apply _ i x hxW a
  have hgb : (deningerRationalWittPresheaf F).germ W x hxW
        ((deningerRationalWittPresheaf F).map i.op b)
      = (deningerRationalWittPresheaf F).germ V x hxV b :=
    TopCat.Presheaf.germ_res_apply _ i x hxW b
  rw [← hga, ← hgb, hab]

set_option backward.isDefEq.respectTransparency false in
/-- The comparison to the rational Witt ring of the stalk is injective. -/
theorem deningerWittStalkToStalk_injective :
    Function.Injective (deningerWittStalkToStalk F x) := by
  intro z z' hzz
  obtain ⟨U, hxU, w, rfl⟩ := (deningerRationalWittPresheaf F).exists_germ_eq z
  obtain ⟨U', hxU', w', rfl⟩ := (deningerRationalWittPresheaf F).exists_germ_eq z'
  have hxV : x ∈ U ⊓ U' := ⟨hxU, hxU'⟩
  set a := (deningerRationalWittPresheaf F).map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op w with ha
  set b := (deningerRationalWittPresheaf F).map (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op w' with hb
  have hga : (deningerRationalWittPresheaf F).germ (U ⊓ U') x hxV a
      = (deningerRationalWittPresheaf F).germ U x hxU w :=
    TopCat.Presheaf.germ_res_apply _ _ x hxV w
  have hgb : (deningerRationalWittPresheaf F).germ (U ⊓ U') x hxV b
      = (deningerRationalWittPresheaf F).germ U' x hxU' w' :=
    TopCat.Presheaf.germ_res_apply _ _ x hxV w'
  rw [← hga, ← hgb]
  refine deningerWittStalkToStalk_germ_inj F x (U ⊓ U') hxV a b ?_
  have hva : deningerCanonicalRationalWittMap (F.germ (U ⊓ U') x hxV).hom a
      = deningerWittStalkToStalk F x
        ((deningerRationalWittPresheaf F).germ (U ⊓ U') x hxV a) := by
    rw [← ConcreteCategory.comp_apply, deningerWittStalkToStalk_germ]
    rfl
  have hvb : deningerCanonicalRationalWittMap (F.germ (U ⊓ U') x hxV).hom b
      = deningerWittStalkToStalk F x
        ((deningerRationalWittPresheaf F).germ (U ⊓ U') x hxV b) := by
    rw [← ConcreteCategory.comp_apply, deningerWittStalkToStalk_germ]
    rfl
  rw [hva, hvb, hga, hgb]
  exact hzz

set_option backward.isDefEq.respectTransparency false in
/-- **The rational Witt construction commutes with stalks.** -/
instance deningerWittStalkToStalk_isIso : IsIso (deningerWittStalkToStalk F x) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    ⟨deningerWittStalkToStalk_injective F x, deningerWittStalkToStalk_surjective F x⟩

variable (Y : AlgebraicGeometry.Scheme.{u})

set_option backward.isDefEq.respectTransparency false in
/-- **The stalk of the rational Witt sheaf is the rational Witt ring of the stalk.** -/
instance deningerWittSheafStalkToStalk_isIso (z : Y) :
    IsIso (deningerWittSheafStalkToStalk Y z) := by
  rw [deningerWittSheafStalkToStalk]
  infer_instance

end RHTower
