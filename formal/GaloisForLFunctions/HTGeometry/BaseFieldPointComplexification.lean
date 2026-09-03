import GaloisForLFunctions.HTGeometry.ComplexPointRationalFunctionEvaluation

/-!
# Complexification of a base-field-valued scheme point

A point of a scheme over a field `k` is algebraic over that base precisely when its complex-valued
point factors through a section `Spec k ⟶ X`.  This module records that factorization without
replacing it by algebraicity of finitely many coordinate values.
-/

namespace AlgebraicGeometry

open CategoryTheory

noncomputable section

/-- A point of a scheme valued in its base field and lying over the identity base point. -/
structure Scheme.BaseFieldPointOver (k : Type) [Field k]
    (X : Scheme) (s : X ⟶ Spec (.of k)) where
  hom : Spec (.of k) ⟶ X
  commutes : hom ≫ s = 𝟙 (Spec (.of k))

/-- Underlying scheme point of a base-field-valued point. -/
def Scheme.BaseFieldPointOver.center
    {k : Type} [Field k] {X : Scheme} {s : X ⟶ Spec (.of k)}
    (p : X.BaseFieldPointOver k s) : X :=
  p.hom (genericPoint (Spec (.of k)))

/-- Scalar extension of a base-field-valued point to a complex-valued point. -/
def Scheme.BaseFieldPointOver.toComplexPoint
    {k : Type} [Field k] [Algebra k ℂ]
    {X : Scheme} {s : X ⟶ Spec (.of k)}
    (p : X.BaseFieldPointOver k s) : X.ComplexPointOver k s where
  hom := Spec.map (CommRingCat.ofHom (algebraMap k ℂ)) ≫ p.hom
  commutes := by
    rw [Category.assoc, p.commutes, Category.comp_id]

/-- The underlying complex point is literally obtained by precomposing with scalar extension. -/
theorem Scheme.BaseFieldPointOver.toComplexPoint_hom
    {k : Type} [Field k] [Algebra k ℂ]
    {X : Scheme} {s : X ⟶ Spec (.of k)}
    (p : X.BaseFieldPointOver k s) :
    p.toComplexPoint.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k ℂ)) ≫ p.hom := rfl

/-- Complexification does not change the underlying center of a base-field point. -/
theorem Scheme.BaseFieldPointOver.toComplexPoint_center
    {k : Type} [Field k] [Algebra k ℂ]
    {X : Scheme} {s : X ⟶ Spec (.of k)}
    (p : X.BaseFieldPointOver k s) :
    p.toComplexPoint.hom.center = p.center := by
  unfold Scheme.ComplexPoint.center Scheme.BaseFieldPointOver.center
  change p.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k ℂ))
        (genericPoint (Spec (.of ℂ)))) =
    p.hom (genericPoint (Spec (.of k)))
  congr 1
  exact Subsingleton.elim _ _

/-- Stalk evaluation is invariant under transporting a complex point and its germ along an
equality of scheme morphisms. -/
theorem Scheme.ComplexPoint.stalkEval_transport
    {X : Scheme} {p q : X.ComplexPoint} (h : p = q)
    (g : X.presheaf.stalk p.center) :
    p.stalkEval g = q.stalkEval (h ▸ g) := by
  subst q
  rfl

/-- The canonical field-stalk equivalence is the structure-sheaf map on field elements. -/
theorem Scheme.specFieldStalkEquiv_apply
    (K : Type) [Field K] (q : Spec (.of K)) (a : K) :
    HTGeometry.specFieldStalkEquiv K q a =
      (StructureSheaf.toStalk K q).hom a := by
  unfold HTGeometry.specFieldStalkEquiv HTGeometry.specStalkRingEquiv
  simp only [RingEquiv.trans_apply]
  let e : K ≃ₐ[K] Localization.AtPrime q.asIdeal :=
    IsLocalization.atUnits (R := K) (S := Localization.AtPrime q.asIdeal)
      q.asIdeal.primeCompl (by
        intro c hc
        have hbot : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime q.asIdeal
        have hne : c ≠ 0 := by
          intro h
          apply hc
          rw [h, hbot]
          exact Ideal.zero_mem _
        exact ⟨Units.mk0 c hne, rfl⟩)
  change (StructureSheaf.stalkIso K q) (e a) = _
  have he : e a = algebraMap K (Localization.AtPrime q.asIdeal) a := by
    simpa using e.commutes a
  rw [he]
  exact (StructureSheaf.stalkIso K q).commutes a

/-- Stalk maps carry the germ of a section to the germ of its pulled-back section. -/
theorem Scheme.Hom.stalkMap_germ_apply
    {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) (x : X)
    (hx : f x ∈ U) (r : Γ(Y, U)) :
    (f.stalkMap x).hom (Y.presheaf.germ U (f x) hx r) =
      X.presheaf.germ (f ⁻¹ᵁ U) x hx ((f.app U).hom r) := by
  have hmap :
      Y.presheaf.germ U (f x) hx ≫ f.stalkMap x =
        f.app U ≫ X.presheaf.germ (f ⁻¹ᵁ U) x hx := by
    change Y.presheaf.germ U (f x) hx ≫
        ((TopCat.Presheaf.stalkFunctor CommRingCat (f x)).map f.c ≫
          TopCat.Presheaf.stalkPushforward CommRingCat f.1.base
            X.presheaf x) = _
    rw [← Category.assoc]
    rw [TopCat.Presheaf.stalkFunctor_map_germ]
    erw [Category.assoc]
    erw [TopCat.Presheaf.stalkPushforward_germ]
    rfl
  exact congrArg (fun g : Γ(Y, U) ⟶ X.presheaf.stalk x => g.hom r) hmap

/-- Evaluation on field-spectrum stalks commutes with scalar extension. -/
theorem Scheme.specMap_stalkEval
    {k : Type} [Field k] [Algebra k ℂ]
    (z : (Spec (.of k)).presheaf.stalk
      (Spec.map (CommRingCat.ofHom (algebraMap k ℂ))
        (genericPoint (Spec (.of ℂ))))) :
    (HTGeometry.specFieldStalkEquiv ℂ
      (genericPoint (Spec (.of ℂ)))).symm
        (((Spec.map (CommRingCat.ofHom (algebraMap k ℂ))).stalkMap
          (genericPoint (Spec (.of ℂ)))).hom z) =
      algebraMap k ℂ
        ((HTGeometry.specFieldStalkEquiv k
          (Spec.map (CommRingCat.ofHom (algebraMap k ℂ))
            (genericPoint (Spec (.of ℂ))))).symm z) := by
  let q := Spec.map (CommRingCat.ofHom (algebraMap k ℂ))
    (genericPoint (Spec (.of ℂ)))
  let eK := HTGeometry.specFieldStalkEquiv k q
  let eC := HTGeometry.specFieldStalkEquiv ℂ (genericPoint (Spec (.of ℂ)))
  let a := eK.symm z
  have hz : z = eK a := (eK.apply_symm_apply z).symm
  rw [hz]
  rw [show eK a = (StructureSheaf.toStalk k q).hom a by
    exact Scheme.specFieldStalkEquiv_apply k q a]
  have hbase : eK.symm ((StructureSheaf.toStalk k q).hom a) = a := by
    rw [← Scheme.specFieldStalkEquiv_apply k q a]
    exact eK.symm_apply_apply a
  rw [hbase]
  apply eC.injective
  rw [eC.apply_symm_apply]
  rw [Scheme.specFieldStalkEquiv_apply ℂ _ _]
  change ((Spec.map (CommRingCat.ofHom (algebraMap k ℂ))).stalkMap
      (genericPoint (Spec (.of ℂ)))).hom
      ((Spec (.of k)).presheaf.germ ⊤ q trivial
        ((Scheme.ΓSpecIso (.of k)).inv.hom a)) =
    (Spec (.of ℂ)).presheaf.germ ⊤ (genericPoint (Spec (.of ℂ))) trivial
      ((Scheme.ΓSpecIso (.of ℂ)).inv.hom (algebraMap k ℂ a))
  rw [Scheme.Hom.stalkMap_germ_apply]
  simp only [TopologicalSpace.Opens.map_top]
  congr 1
  have hnat := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap k ℂ))
  exact congrArg
    (fun g : CommRingCat.of k ⟶ Γ(Spec (.of ℂ), ⊤) => g.hom a) hnat.symm

/-- Evaluation of a germ at a base-field point before scalar extension.  The source stalk is
written at the complexified center so no untracked equality transport occurs. -/
noncomputable def Scheme.BaseFieldPointOver.stalkEvalAtComplexCenter
    {k : Type} [Field k] [Algebra k ℂ]
    {X : Scheme} {s : X ⟶ Spec (.of k)}
    (p : X.BaseFieldPointOver k s) :
    X.presheaf.stalk p.toComplexPoint.hom.center →+* k :=
  (HTGeometry.specFieldStalkEquiv k
      (Spec.map (CommRingCat.ofHom (algebraMap k ℂ))
        (genericPoint (Spec (.of ℂ))))).symm.toRingHom.comp
    (p.hom.stalkMap
      (Spec.map (CommRingCat.ofHom (algebraMap k ℂ))
        (genericPoint (Spec (.of ℂ))))).hom

/-- Stalk evaluation at a complexified base-field point is the scalar extension of its literal
base-field value. -/
theorem Scheme.BaseFieldPointOver.toComplexPoint_stalkEval
    {k : Type} [Field k] [Algebra k ℂ]
    {X : Scheme} {s : X ⟶ Spec (.of k)}
    (p : X.BaseFieldPointOver k s)
    (g : X.presheaf.stalk p.toComplexPoint.hom.center) :
    p.toComplexPoint.hom.stalkEval g =
      algebraMap k ℂ (p.stalkEvalAtComplexCenter g) := by
  unfold Scheme.ComplexPoint.stalkEval
  unfold Scheme.BaseFieldPointOver.stalkEvalAtComplexCenter
  simp only [RingHom.comp_apply]
  change (HTGeometry.specFieldStalkEquiv ℂ
      (genericPoint (Spec (.of ℂ)))).symm
      ((((Spec.map (CommRingCat.ofHom (algebraMap k ℂ))) ≫ p.hom).stalkMap
        (genericPoint (Spec (.of ℂ)))).hom g) = _
  rw [Scheme.Hom.stalkMap_comp]
  exact Scheme.specMap_stalkEval
    (((p.hom.stalkMap
      (Spec.map (CommRingCat.ofHom (algebraMap k ℂ))
        (genericPoint (Spec (.of ℂ)))))).hom g)

end

end AlgebraicGeometry
