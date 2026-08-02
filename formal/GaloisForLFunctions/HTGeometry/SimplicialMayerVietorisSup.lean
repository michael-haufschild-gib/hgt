import GaloisForLFunctions.HTGeometry.SimplicialMayerVietoris
import GaloisForLFunctions.HTGeometry.CoproductMayerVietorisSup

/-!
# Mayer--Vietoris for chain complexes of subcomplexes, over the union

The Mayer--Vietoris short exact sequence of two subcomplexes, with the union of the two in place of
the ambient simplicial set.  No covering hypothesis is needed.

This is what an iterated cover consumes: the pieces of a many-piece cover are subcomplexes of a
partial union, not of the whole.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u w

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable (X : SSet.{w}) (R : C) (A B : X.Subcomplex)

/-- The difference of the two inclusions into the union. -/
noncomputable def mvSupChainSnd :
    (A : SSet.{w}).chainComplex R ⊞ (B : SSet.{w}).chainComplex R ⟶
      ((A ⊔ B : X.Subcomplex) : SSet.{w}).chainComplex R :=
  biprod.desc (SSet.chainComplexMap (SSet.Subcomplex.homOfLE le_sup_left) R)
    (-SSet.chainComplexMap (SSet.Subcomplex.homOfLE le_sup_right) R)

theorem homOfLE_comp_homOfLE_eq :
    (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
        ≫ SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)
      = SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)
        ≫ SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B) := by
  refine (cancel_mono ((A ⊔ B : X.Subcomplex).ι)).1 ?_
  rw [Category.assoc, Category.assoc, SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.homOfLE_ι,
    SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.homOfLE_ι]

theorem mvChainFst_comp_mvSupChainSnd :
    mvChainFst X R A B ≫ mvSupChainSnd X R A B = 0 := by
  rw [mvChainFst, mvSupChainSnd, biprod.lift_desc, Preadditive.comp_neg,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    homOfLE_comp_homOfLE_eq X A B, add_neg_cancel]

/-- The Mayer--Vietoris short complex over the union. -/
noncomputable def mvSupChainShortComplex : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk _ _ (mvChainFst_comp_mvSupChainSnd X R A B)

@[simp] theorem mvSupChainShortComplex_f :
    (mvSupChainShortComplex X R A B).f = mvChainFst X R A B := rfl

@[simp] theorem mvSupChainShortComplex_g :
    (mvSupChainShortComplex X R A B).g = mvSupChainSnd X R A B := rfl

/-- In degree `n` the second map is the second map of the coproduct short complex over the union. -/
theorem mvSupChainSnd_f (n : ℕ) :
    (HomologicalComplex.biprodXIso ((A : SSet.{w}).chainComplex R)
        ((B : SSet.{w}).chainComplex R) n).inv ≫ (mvSupChainSnd X R A B).f n
      = mvSupSnd R (A.obj (op ⦋n⦌)) (B.obj (op ⦋n⦌)) := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · erw [← Category.assoc, HomologicalComplex.inl_biprodXIso_inv, mvSupChainSnd,
      HomologicalComplex.biprod_inl_desc_f, chainComplexMap_homOfLE_f, mvSupSnd, biprod.inl_desc]
  · erw [← Category.assoc, HomologicalComplex.inr_biprodXIso_inv, mvSupChainSnd,
      HomologicalComplex.biprod_inr_desc_f, HomologicalComplex.neg_f_apply,
      chainComplexMap_homOfLE_f, mvSupSnd, biprod.inr_desc]
    rfl

/-- In each degree it is the split short complex of coproducts over the union. -/
noncomputable def mvSupChainShortComplexIso (n : ℕ) :
    mvSupShortComplex R (A.obj (op ⦋n⦌)) (B.obj (op ⦋n⦌))
      ≅ (mvSupChainShortComplex X R A B).map (HomologicalComplex.eval C _ n) := by
  refine ShortComplex.isoMk (Iso.refl _)
    (HomologicalComplex.biprodXIso ((A : SSet.{w}).chainComplex R)
      ((B : SSet.{w}).chainComplex R) n).symm (Iso.refl _) ?_ ?_
  · rw [Iso.refl_hom]
    erw [Category.id_comp]
    exact mvChainFst_f X R A B n
  · rw [Iso.refl_hom]
    erw [Category.comp_id]
    exact mvSupChainSnd_f X R A B n

/-- **The Mayer--Vietoris short exact sequence over the union**, with no covering hypothesis. -/
theorem mvSupChainShortExact : (mvSupChainShortComplex X R A B).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n =>
    ShortComplex.shortExact_of_iso (mvSupChainShortComplexIso X R A B n)
      (mvSupShortExact R _ _))

/-- **Vanishing from Mayer--Vietoris, over the union.** -/
theorem isZero_homology_of_mayerVietoris_sup (i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel i j)
    (hA : Limits.IsZero (((A : SSet.{w}).chainComplex R).homology i))
    (hB : Limits.IsZero (((B : SSet.{w}).chainComplex R).homology i))
    (hAB : Limits.IsZero ((((A ⊓ B : X.Subcomplex) : SSet.{w}).chainComplex R).homology j)) :
    Limits.IsZero ((((A ⊔ B : X.Subcomplex) : SSet.{w}).chainComplex R).homology i) := by
  have hS := mvSupChainShortExact X R A B
  exact ((hS.homology_exact₃ i j hij).isZero_X₂
    ((isZero_homology_biprod _ _ i hA hB).eq_zero_of_src _) (hAB.eq_zero_of_tgt _))

end

end GaloisForLFunctions.HTGeometry
