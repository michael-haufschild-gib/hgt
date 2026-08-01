import GaloisForLFunctions.HTGeometry.CoproductMayerVietoris
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence

/-!
# Chains on a subcomplex are the coproduct over its simplices

The chain complex of a subcomplex has, in each degree, the coproduct over that degree's simplices as
its object, and the maps induced by inclusions of subcomplexes are the maps induced by the inclusions
of index sets.  Two subcomplexes covering a simplicial set cover its simplices in each degree.

These identifications turn the split short exact sequence of coproducts into a degreewise split short
exact sequence of chain complexes, which is the Mayer--Vietoris input.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [HasCoproducts.{w} C]
variable (X : SSet.{w}) (R : C)

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- **The `n`-chains of a subcomplex are the coproduct over its `n`-simplices.** -/
theorem chainComplex_X_eq (A : X.Subcomplex) (n : ℕ) :
    ((A : SSet.{w}).chainComplex R).X n = subCoproduct R (A.obj (op ⦋n⦌)) := rfl

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- **The chain map induced by the inclusion of a subcomplex is the map induced by the inclusion of
its simplices.** -/
theorem chainComplexMap_ι_f (A : X.Subcomplex) (n : ℕ) :
    (SSet.chainComplexMap A.ι R).f n = inclFull R (A.obj (op ⦋n⦌)) := by
  refine Sigma.hom_ext _ _ (fun x => ?_)
  exact (SSet.ι_chainComplexMap_f _ _ A.ι R x).trans (ι_inclFull R (A.obj (op ⦋n⦌)) x).symm

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- **And the chain map induced by an inclusion of subcomplexes likewise.** -/
theorem chainComplexMap_homOfLE_f {A B : X.Subcomplex} (h : A ≤ B) (n : ℕ) :
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE h) R).f n
      = inclCop R (show A.obj (op ⦋n⦌) ⊆ B.obj (op ⦋n⦌) from fun _ hx => h _ hx) := by
  refine Sigma.hom_ext _ _ (fun x => ?_)
  exact (SSet.ι_chainComplexMap_f _ _ _ R x).trans
    (ι_inclCop R (show A.obj (op ⦋n⦌) ⊆ B.obj (op ⦋n⦌) from fun _ hx => h _ hx) x).symm

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- **Two subcomplexes covering a simplicial set cover its simplices in every degree.** -/
theorem subcomplex_obj_union {A B : X.Subcomplex} (h : A ⊔ B = ⊤) (n : ℕ) :
    A.obj (op ⦋n⦌) ∪ B.obj (op ⦋n⦌) = Set.univ := by
  have hobj : (A ⊔ B).obj (op ⦋n⦌) = A.obj (op ⦋n⦌) ∪ B.obj (op ⦋n⦌) := rfl
  rw [← hobj, h]
  rfl

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- **And their intersection is the intersection of the simplices.** -/
theorem subcomplex_obj_inter (A B : X.Subcomplex) (n : ℕ) :
    (A ⊓ B).obj (op ⦋n⦌) = A.obj (op ⦋n⦌) ∩ B.obj (op ⦋n⦌) := rfl

/-! ## The Mayer--Vietoris short exact sequence of chain complexes -/

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable (X : SSet.{w}) (R : C) (A B : X.Subcomplex)

/-- The two inclusions of the intersection. -/
noncomputable def mvChainFst :
    ((A ⊓ B : X.Subcomplex) : SSet.{w}).chainComplex R ⟶
      (A : SSet.{w}).chainComplex R ⊞ (B : SSet.{w}).chainComplex R :=
  biprod.lift (SSet.chainComplexMap (SSet.Subcomplex.homOfLE inf_le_left) R)
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE inf_le_right) R)

/-- The difference of the two inclusions into the ambient simplicial set. -/
noncomputable def mvChainSnd :
    (A : SSet.{w}).chainComplex R ⊞ (B : SSet.{w}).chainComplex R ⟶ X.chainComplex R :=
  biprod.desc (SSet.chainComplexMap A.ι R) (-SSet.chainComplexMap B.ι R)

theorem mvChainFst_comp_mvChainSnd : mvChainFst X R A B ≫ mvChainSnd X R A B = 0 := by
  rw [mvChainFst, mvChainSnd, biprod.lift_desc, Preadditive.comp_neg,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.homOfLE_ι, add_neg_cancel]

/-- The Mayer--Vietoris short complex of chain complexes. -/
noncomputable def mvChainShortComplex : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk _ _ (mvChainFst_comp_mvChainSnd X R A B)

@[simp] theorem mvChainShortComplex_f :
    (mvChainShortComplex X R A B).f = mvChainFst X R A B := rfl

@[simp] theorem mvChainShortComplex_g :
    (mvChainShortComplex X R A B).g = mvChainSnd X R A B := rfl

/-- In degree `n` the first map is the first map of the coproduct short complex. -/
theorem mvChainFst_f (n : ℕ) :
    (mvChainFst X R A B).f n
      = mvFst R (A.obj (op ⦋n⦌)) (B.obj (op ⦋n⦌))
        ≫ (HomologicalComplex.biprodXIso ((A : SSet.{w}).chainComplex R)
            ((B : SSet.{w}).chainComplex R) n).inv := by
  refine HomologicalComplex.biprodX_ext_to ?_ ?_
  · rw [mvChainFst, HomologicalComplex.biprod_lift_fst_f, chainComplexMap_homOfLE_f]
    erw [Category.assoc, ← HomologicalComplex.biprodXIso_hom_fst, Iso.inv_hom_id_assoc, mvFst,
      biprod.lift_fst]
  · rw [mvChainFst, HomologicalComplex.biprod_lift_snd_f, chainComplexMap_homOfLE_f]
    erw [Category.assoc, ← HomologicalComplex.biprodXIso_hom_snd, Iso.inv_hom_id_assoc, mvFst,
      biprod.lift_snd]

/-- In degree `n` the second map is the second map of the coproduct short complex. -/
theorem mvChainSnd_f (n : ℕ) :
    (HomologicalComplex.biprodXIso ((A : SSet.{w}).chainComplex R)
        ((B : SSet.{w}).chainComplex R) n).inv ≫ (mvChainSnd X R A B).f n
      = mvSnd R (A.obj (op ⦋n⦌)) (B.obj (op ⦋n⦌)) := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · erw [← Category.assoc, HomologicalComplex.inl_biprodXIso_inv, mvChainSnd,
      HomologicalComplex.biprod_inl_desc_f, chainComplexMap_ι_f, mvSnd, biprod.inl_desc]
  · erw [← Category.assoc, HomologicalComplex.inr_biprodXIso_inv, mvChainSnd,
      HomologicalComplex.biprod_inr_desc_f, HomologicalComplex.neg_f_apply, chainComplexMap_ι_f,
      mvSnd, biprod.inr_desc]
    rfl

/-- In each degree it is the split short complex of coproducts. -/
noncomputable def mvChainShortComplexIso (n : ℕ) :
    mvShortComplex R (A.obj (op ⦋n⦌)) (B.obj (op ⦋n⦌))
      ≅ (mvChainShortComplex X R A B).map (HomologicalComplex.eval C _ n) := by
  refine ShortComplex.isoMk (Iso.refl _)
    (HomologicalComplex.biprodXIso ((A : SSet.{w}).chainComplex R)
      ((B : SSet.{w}).chainComplex R) n).symm (Iso.refl _) ?_ ?_
  · rw [Iso.refl_hom]
    erw [Category.id_comp]
    exact mvChainFst_f X R A B n
  · rw [Iso.refl_hom]
    erw [Category.comp_id]
    exact mvChainSnd_f X R A B n

/-- **The Mayer--Vietoris short exact sequence of chain complexes.**  Two subcomplexes covering a
simplicial set give a short exact sequence of singular chain complexes, degreewise split. -/
theorem mvChainShortExact (h : A ⊔ B = ⊤) : (mvChainShortComplex X R A B).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n =>
    ShortComplex.shortExact_of_iso (mvChainShortComplexIso X R A B n)
      (mvShortExact R _ _ (subcomplex_obj_union X h n)))

/-! ## Vanishing from Mayer--Vietoris -/

omit [HasCoproducts.{w} C] in
/-- **The homology of a biproduct of complexes vanishes when both summands' does.** -/
theorem isZero_homology_biprod (K L : ChainComplex C ℕ) (i : ℕ)
    (hK : Limits.IsZero (K.homology i)) (hL : Limits.IsZero (L.homology i)) :
    Limits.IsZero ((K ⊞ L).homology i) := by
  rw [Limits.IsZero.iff_id_eq_zero]
  have hid : HomologicalComplex.homologyMap (𝟙 (K ⊞ L)) i = 𝟙 _ :=
    HomologicalComplex.homologyMap_id _ _
  rw [← hid, ← biprod.total, HomologicalComplex.homologyMap_add,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    hK.eq_zero_of_tgt (HomologicalComplex.homologyMap (biprod.fst : K ⊞ L ⟶ K) i),
    hL.eq_zero_of_tgt (HomologicalComplex.homologyMap (biprod.snd : K ⊞ L ⟶ L) i),
    Limits.zero_comp, Limits.zero_comp, add_zero]

/-- **Mayer--Vietoris vanishing.**  If the two pieces have no homology in degree `i` and their
intersection has none in degree `i - 1`, then neither has the whole simplicial set in degree `i`. -/
theorem isZero_homology_of_mayerVietoris (h : A ⊔ B = ⊤) (i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel i j)
    (hA : Limits.IsZero (((A : SSet.{w}).chainComplex R).homology i))
    (hB : Limits.IsZero (((B : SSet.{w}).chainComplex R).homology i))
    (hAB : Limits.IsZero ((((A ⊓ B : X.Subcomplex) : SSet.{w}).chainComplex R).homology j)) :
    Limits.IsZero ((X.chainComplex R).homology i) := by
  have hS := mvChainShortExact X R A B h
  exact ((hS.homology_exact₃ i j hij).isZero_X₂
    ((isZero_homology_biprod _ _ i hA hB).eq_zero_of_src _) (hAB.eq_zero_of_tgt _))

/-- **Mayer--Vietoris vanishing without a vanishing intersection.**  If the two pieces have no
homology in degree `i` and the comparison map from the intersection's homology in degree `i - 1` is
a monomorphism, then the whole simplicial set has no homology in degree `i`.

This replaces the hypothesis that the intersection is acyclic in degree `i - 1` — which fails in
degree `0`, where the homology of a connected piece is a copy of the coefficients — by the injectivity
that the reduced statement would express. -/
theorem isZero_homology_of_mayerVietoris_mono (h : A ⊔ B = ⊤) (i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel i j)
    (hA : Limits.IsZero (((A : SSet.{w}).chainComplex R).homology i))
    (hB : Limits.IsZero (((B : SSet.{w}).chainComplex R).homology i))
    (hmono : Mono (HomologicalComplex.homologyMap (mvChainShortComplex X R A B).f j)) :
    Limits.IsZero ((X.chainComplex R).homology i) := by
  have hS := mvChainShortExact X R A B h
  haveI := hmono
  have hdelta : hS.δ i j hij = 0 := zero_of_comp_mono _ (hS.δ_comp i j hij)
  exact (hS.homology_exact₃ i j hij).isZero_X₂
    ((isZero_homology_biprod _ _ i hA hB).eq_zero_of_src _) hdelta

end

end GaloisForLFunctions.HTGeometry
