import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RationalValueDenominators
import GaloisForLFunctions.HTGeometry.AlgebraicGroupGenericPoint

/-! A correspondence fixes a rational point exactly when its two pullbacks
have the same values on the affine chart of the first image. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open GaloisForLFunctions.HTGeometry GlobalTheory.SchemeCohomology

namespace GlobalTheory.WH

variable {K : Type} [Field K] {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y]
  {s : Z ⟶ Spec (CommRingCat.of K)} {t : Y ⟶ Spec (CommRingCat.of K)} [IsSeparated s]
  [Algebra K Y.functionField] {U : Z.Opens} {c₁ c₂ : Y ⟶ Z} [IsDominant c₂]

omit [IsIntegral Z] [IsSeparated s] in
private theorem specMap_affinePointEval (hU : IsAffineOpen U) (z : Z.BaseFieldPointOver K s)
    (hz : z.hom default ∈ U) :
    Spec.map (CommRingCat.ofHom (affinePointEval z hz).toRingHom) ≫ hU.fromSpec = z.hom := by
  have h : CommRingCat.ofHom (affinePointEval z hz).toRingHom =
      Z.presheaf.germ U (z.hom default) hz ≫ localPointEval z := by
    apply CommRingCat.hom_ext
    ext a
    exact (localPointEval_germ z hz a).symm
  let g : Γ(Z, U) ⟶ Z.presheaf.stalk (z.hom default) :=
    Z.presheaf.germ U (z.hom default) hz
  let l := localPointEval z
  calc
    _ = Spec.map (g ≫ l) ≫ hU.fromSpec :=
      congrArg (fun f : Γ(Z, U) ⟶ CommRingCat.of K => Spec.map f ≫ hU.fromSpec) h
    _ = Spec.map l ≫ Spec.map g ≫ hU.fromSpec := Spec.map_comp_assoc g l _
    _ = Spec.map l ≫ Z.fromSpecStalk (z.hom default) :=
      congrArg (Spec.map l ≫ ·) (hU.fromSpecStalk_eq_fromSpecStalk hz)
    _ = z.hom := specMap_localPointEval_fromSpecStalk z

/-- Clearing denominators on the first inverse-image chart detects equality
of the two rational images. The second image lies on the chart whenever
its pulled-back section ring is regular at the given point. -/
theorem fixed_iff_chart_values (hc₁ : c₁ ≫ s = t) (hU : IsAffineOpen U)
    (hV : IsAffineOpen (c₁ ⁻¹ᵁ U)) (y : Y.BaseFieldPointOver K t)
    (hy : y.hom default ∈ c₁ ⁻¹ᵁ U) (hη : genericPoint Z ∈ U)
    {B : Subalgebra K Y.functionField} (i : SectionRing t (c₁ ⁻¹ᵁ U) ≃ₐ[K] B)
    (e : B →ₐ[K] K)
    (hg : ∀ b, (i b : Y.functionField) =
      (Y.presheaf.germ _ (genericPoint Y) ((genericPoint_specializes (y.hom default)).mem_open
        (c₁ ⁻¹ᵁ U).isOpen hy)).hom b)
    (he : ∀ b, e (i b) = affinePointEval y hy b) :
    (∀ a : Γ(Z, U), Val B e
      (c₂.functionFieldPullback.hom ((Z.presheaf.germ U (genericPoint Z) hη).hom a))
      (affinePointEval (mapBaseFieldPoint hc₁ y) hy a)) ↔ y.hom ≫ c₁ = y.hom ≫ c₂ := by
  let P := y.hom default
  let j := stalkToFunctionField P
  let l := localPointEval y
  let g := Z.presheaf.germ U (genericPoint Z) hη
  let v : Γ(Z, U) →+* Y.functionField := (g ≫ c₂.functionFieldPullback).hom
  let z₁ := mapBaseFieldPoint hc₁ y
  let χ := affinePointEval z₁ hy
  constructor
  · intro h
    have hloc (a : Γ(Z, U)) : ∃ u : Y.presheaf.stalk P, j.hom u = v a ∧ l.hom u = χ a :=
      (val_iff_exists_local hV y hy i e hg he (v a) (χ a)).mp (h a)
    have hinj := stalkToFunctionField_injective P
    let h₀ := RingEquiv.ofBijective j.hom.rangeRestrict
      ⟨fun _ _ h => hinj (congrArg Subtype.val h), fun u => by
        obtain ⟨a, ha⟩ := u.2
        exact ⟨a, Subtype.ext ha⟩⟩
    let F : Γ(Z, U) →+* Y.presheaf.stalk P :=
      h₀.symm.toRingHom.comp (v.codRestrict j.hom.range fun a => by
        obtain ⟨u, hu, _⟩ := hloc a
        exact ⟨u, hu⟩)
    have hF (a : Γ(Z, U)) : j.hom (F a) = v a :=
      congrArg Subtype.val (h₀.apply_symm_apply _)
    have hEval (a : Γ(Z, U)) : l.hom (F a) = χ a := by
      obtain ⟨u, hu, huv⟩ := hloc a
      rw [hinj ((hF a).trans hu.symm)]
      exact huv
    let ff : Γ(Z, U) ⟶ Y.presheaf.stalk P := CommRingCat.ofHom F
    have hfj : ff ≫ j = g ≫ c₂.functionFieldPullback :=
      CommRingCat.hom_ext (RingHom.ext hF)
    let m := Spec.map ff ≫ hU.fromSpec
    have hgen : Spec.map j ≫ m = Spec.map j ≫ Y.fromSpecStalk P ≫ c₂ := calc
      _ = Spec.map (g ≫ c₂.functionFieldPullback) ≫ hU.fromSpec := by
        rw [show m = Spec.map ff ≫ hU.fromSpec from rfl, ← Spec.map_comp_assoc, hfj]
      _ = Spec.map c₂.functionFieldPullback ≫ Z.fromSpecStalk (genericPoint Z) := by
        rw [Spec.map_comp, Category.assoc]
        exact congrArg (Spec.map c₂.functionFieldPullback ≫ ·)
          (hU.fromSpecStalk_eq_fromSpecStalk hη)
      _ = Y.fromSpecStalk (genericPoint Y) ≫ c₂ :=
        Scheme.Hom.specMap_functionFieldPullback_fromSpecStalk c₂
      _ = _ := (Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc
        (genericPoint_specializes P) c₂).symm
    letI : IsDominant (Spec.map j) := isDominant_specMap_stalkToFunctionField P
    haveI : IsSeparated (terminal.from Z) := by
      rw [← terminal.comp_from s]
      infer_instance
    have hm : m = Y.fromSpecStalk P ≫ c₂ :=
      ext_of_isDominant_of_isSeparated (terminal.from Z) (Subsingleton.elim _ _)
        (Spec.map j) hgen
    have hfl : ff ≫ l = CommRingCat.ofHom χ.toRingHom :=
      CommRingCat.hom_ext (RingHom.ext hEval)
    calc
      y.hom ≫ c₁ = Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ hU.fromSpec :=
        (specMap_affinePointEval hU z₁ hy).symm
      _ = Spec.map l ≫ m := by
        exact (congrArg (fun f : Γ(Z, U) ⟶ CommRingCat.of K => Spec.map f ≫ hU.fromSpec)
          hfl.symm).trans (Spec.map_comp_assoc ff l _)
      _ = y.hom ≫ c₂ := by
        rw [hm, ← Category.assoc, specMap_localPointEval_fromSpecStalk]
  · intro h a
    have hy₂ : y.hom default ∈ c₂ ⁻¹ᵁ U := by
      change (y.hom ≫ c₂) default ∈ U
      rw [← h]
      exact hy
    apply (val_iff_exists_local hV y hy i e hg he (v a) (χ a)).mpr
    let a₂ := (c₂.app U).hom a
    refine ⟨(Y.presheaf.germ (c₂ ⁻¹ᵁ U) P hy₂).hom a₂, ?_, ?_⟩
    · exact (ConcreteCategory.congr_hom
        (Y.presheaf.germ_stalkSpecializes hy₂ (genericPoint_specializes P)) a₂).trans
        (c₂.functionFieldPullback_germ U hη a).symm
    · rw [localPointEval_germ y hy₂]
      have h' := pointEval_comp y.hom c₂ U hy₂ a
      change pointEval y.hom (c₂ ⁻¹ᵁ U) hy₂ a₂ = pointEval (y.hom ≫ c₁) U hy a
      exact h'.symm.trans (pointEval_congr h.symm U hy₂ hy a)

end GlobalTheory.WH
