import GaloisForLFunctions.HTGeometry.CoproductMayerVietoris

/-!
# Mayer--Vietoris for coproducts, over the union rather than the whole type

The split short exact sequence of the previous module, with the coproduct over the *union* of the two
subsets in place of the coproduct over the whole ambient type.  No covering hypothesis is needed: the
union covers itself.

This is the form an iterated cover needs, where the two pieces are subcomplexes of a larger one
rather than of the ambient simplicial set.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [HasCoproducts.{w} C]

variable {T : Type w} (R : C) (S₁ S₂ : Set T)

/-- The difference of the two inclusions into the coproduct over the union. -/
noncomputable def mvSupSnd :
    subCoproduct R S₁ ⊞ subCoproduct R S₂ ⟶ subCoproduct R (S₁ ∪ S₂) :=
  biprod.desc (inclCop R Set.subset_union_left) (-inclCop R Set.subset_union_right)

omit [HasZeroObject C] in
theorem mvFst_comp_mvSupSnd : mvFst R S₁ S₂ ≫ mvSupSnd R S₁ S₂ = 0 := by
  refine Sigma.hom_ext _ _ (fun x => ?_)
  simp [mvFst, mvSupSnd, biprod.lift_desc]

/-- The Mayer--Vietoris short complex over the union. -/
noncomputable def mvSupShortComplex : ShortComplex C :=
  ShortComplex.mk _ _ (mvFst_comp_mvSupSnd R S₁ S₂)

omit [HasZeroObject C] in
@[simp] theorem mvSupShortComplex_f : (mvSupShortComplex R S₁ S₂).f = mvFst R S₁ S₂ := rfl

omit [HasZeroObject C] in
@[simp] theorem mvSupShortComplex_g : (mvSupShortComplex R S₁ S₂).g = mvSupSnd R S₁ S₂ := rfl

/-- The section, over the union. -/
noncomputable def mvSupSection :
    subCoproduct R (S₁ ∪ S₂) ⟶ subCoproduct R S₁ ⊞ subCoproduct R S₂ :=
  restr R (S₁ ∪ S₂) S₁ ≫ biprod.inl
    - restr R (S₁ ∪ S₂) (S₂ \ S₁) ≫ inclCop R Set.sdiff_subset ≫ biprod.inr

omit [HasZeroObject C] in
theorem mvSupSection_comp_mvSupSnd : mvSupSection R S₁ S₂ ≫ mvSupSnd R S₁ S₂ = 𝟙 _ := by
  refine Sigma.hom_ext _ _ (fun x => ?_)
  rw [Category.comp_id, mvSupSection, mvSupSnd, Preadditive.sub_comp, Preadditive.comp_sub]
  by_cases hx : (x : T) ∈ S₁
  · rw [Category.assoc, biprod.inl_desc, ι_restr_of_mem_assoc R x hx, ι_inclCop,
      Category.assoc, Category.assoc, biprod.inr_desc,
      ι_restr_of_notMem_assoc R x (by simp [hx]), Limits.zero_comp, sub_zero]
  · have hx2 : (x : T) ∈ S₂ \ S₁ := ⟨Or.resolve_left x.2 hx, hx⟩
    rw [Category.assoc, biprod.inl_desc, ι_restr_of_notMem_assoc R x hx, Limits.zero_comp,
      Category.assoc, Category.assoc, biprod.inr_desc, ι_restr_of_mem_assoc R x hx2,
      ι_inclCop_assoc, Preadditive.comp_neg, ι_inclCop, zero_sub, neg_neg]

omit [HasZeroObject C] in
theorem mvSup_splitting_id :
    mvRetraction R S₁ S₂ ≫ mvFst R S₁ S₂ + mvSupSnd R S₁ S₂ ≫ mvSupSection R S₁ S₂ = 𝟙 _ := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [Preadditive.comp_add, Category.comp_id, mvRetraction, ← Category.assoc, ← Category.assoc,
      biprod.inl_snd, Limits.zero_comp, Limits.zero_comp, zero_add, mvSupSnd, ← Category.assoc,
      biprod.inl_desc]
    refine Sigma.hom_ext _ _ (fun x => ?_)
    rw [← Category.assoc, ι_inclCop, mvSupSection, Preadditive.comp_sub,
      ι_restr_of_mem_assoc R (⟨(x : T), Set.subset_union_left x.2⟩ : (S₁ ∪ S₂ : Set T)) x.2,
      ι_restr_of_notMem_assoc R (⟨(x : T), Set.subset_union_left x.2⟩ : (S₁ ∪ S₂ : Set T))
        (by simp [x.2]), Limits.zero_comp, sub_zero]
  · rw [Preadditive.comp_add, Category.comp_id, mvRetraction, ← Category.assoc, ← Category.assoc,
      biprod.inr_snd, Category.id_comp, mvSupSnd, ← Category.assoc, biprod.inr_desc]
    refine Sigma.hom_ext _ _ (fun x => ?_)
    rw [Preadditive.comp_add, ← Category.assoc, Preadditive.neg_comp, Preadditive.comp_neg,
      ← Category.assoc, ι_inclCop, mvSupSection, Preadditive.comp_sub]
    rw [Category.assoc]
    by_cases hx : (x : T) ∈ S₁
    · rw [ι_restr_of_mem_assoc R x (⟨hx, x.2⟩ : (x : T) ∈ S₁ ∩ S₂), mvFst, biprod.lift_eq,
        Preadditive.comp_add, ι_inclCop_assoc, ι_inclCop_assoc,
        ι_restr_of_mem_assoc R (⟨(x : T), Set.subset_union_right x.2⟩ : (S₁ ∪ S₂ : Set T)) hx,
        ι_restr_of_notMem_assoc R (⟨(x : T), Set.subset_union_right x.2⟩ : (S₁ ∪ S₂ : Set T))
          (by simp [hx]), Limits.zero_comp, sub_zero]
      abel
    · rw [ι_restr_of_notMem_assoc R x (by simp [hx]), Limits.zero_comp, zero_add,
        ι_restr_of_notMem_assoc R (⟨(x : T), Set.subset_union_right x.2⟩ : (S₁ ∪ S₂ : Set T)) hx,
        Limits.zero_comp, zero_sub,
        ι_restr_of_mem_assoc R (⟨(x : T), Set.subset_union_right x.2⟩ : (S₁ ∪ S₂ : Set T))
          ((Set.mem_sdiff _).2 ⟨x.2, hx⟩), neg_neg, ι_inclCop_assoc]

/-- **The Mayer--Vietoris sequence over the union is split.** -/
noncomputable def mvSupSplitting : (mvSupShortComplex R S₁ S₂).Splitting where
  r := mvRetraction R S₁ S₂
  s := mvSupSection R S₁ S₂
  f_r := mvFst_comp_mvRetraction R S₁ S₂
  s_g := mvSupSection_comp_mvSupSnd R S₁ S₂
  id := mvSup_splitting_id R S₁ S₂

/-- **And therefore short exact.** -/
theorem mvSupShortExact : (mvSupShortComplex R S₁ S₂).ShortExact :=
  (mvSupSplitting R S₁ S₂).shortExact

end GaloisForLFunctions.HTGeometry
