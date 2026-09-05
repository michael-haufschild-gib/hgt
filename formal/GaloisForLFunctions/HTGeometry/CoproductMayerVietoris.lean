import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# The Mayer--Vietoris splitting of a coproduct over a covered set

A set covered by two subsets makes the coproducts over the four sets involved into a split short
exact sequence

```text
0 → ∐_{S₁ ∩ S₂} R → (∐_{S₁} R) ⊞ (∐_{S₂} R) → ∐_{S} R → 0.
```

The splitting is elementary — each map is the identity on the basis elements where it is defined and
zero elsewhere — but it is what is missing before a Mayer--Vietoris sequence: the chain complex of a
simplicial set is a coproduct over its simplices in each degree, and two subcomplexes covering it
cover the simplices of each degree.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [HasCoproducts.{w} C]

variable {T : Type w} (R : C)

/-- The coproduct of copies of `R` indexed by a subset. -/
noncomputable abbrev subCoproduct (S : Set T) : C := ∐ (fun _ : S => R)

/-- The map induced by an inclusion of subsets. -/
noncomputable def inclCop {S S' : Set T} (h : S ⊆ S') :
    subCoproduct R S ⟶ subCoproduct R S' :=
  Sigma.desc (fun x => Sigma.ι (fun _ : S' => R) ⟨x, h x.2⟩)

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem ι_inclCop {S S' : Set T} (h : S ⊆ S') (x : S) :
    Sigma.ι (fun _ : S => R) x ≫ inclCop R h = Sigma.ι (fun _ : S' => R) ⟨x, h x.2⟩ :=
  Sigma.ι_desc _ _

open scoped Classical in
/-- The map that is the identity on the basis elements lying in the target subset and zero on the
others. -/
noncomputable def restr (S S' : Set T) : subCoproduct R S ⟶ subCoproduct R S' :=
  Sigma.desc (fun x => if h : (x : T) ∈ S' then Sigma.ι (fun _ : S' => R) ⟨x, h⟩ else 0)

omit [HasZeroObject C] [HasBinaryBiproducts C] in
@[reassoc]
theorem ι_restr_of_mem {S S' : Set T} (x : S) (h : (x : T) ∈ S') :
    Sigma.ι (fun _ : S => R) x ≫ restr R S S' = Sigma.ι (fun _ : S' => R) ⟨x, h⟩ := by
  classical
  rw [restr, Sigma.ι_desc, dif_pos h]

omit [HasZeroObject C] [HasBinaryBiproducts C] in
@[reassoc]
theorem ι_restr_of_notMem {S S' : Set T} (x : S) (h : (x : T) ∉ S') :
    Sigma.ι (fun _ : S => R) x ≫ restr R S S' = 0 := by
  classical
  rw [restr, Sigma.ι_desc, dif_neg h]

/-- The inclusion of a subset's coproduct into the coproduct over the whole type. -/
noncomputable def inclFull (S : Set T) : subCoproduct R S ⟶ ∐ (fun _ : T => R) :=
  Sigma.desc (fun x => Sigma.ι (fun _ : T => R) (x : T))

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem ι_inclFull (S : Set T) (x : S) :
    Sigma.ι (fun _ : S => R) x ≫ inclFull R S = Sigma.ι (fun _ : T => R) (x : T) :=
  Sigma.ι_desc _ _

open scoped Classical in
/-- The map that is the identity on the basis elements of a subset and zero on the others. -/
noncomputable def restrFull (S : Set T) : (∐ fun _ : T => R) ⟶ subCoproduct R S :=
  Sigma.desc (fun t => if h : t ∈ S then Sigma.ι (fun _ : S => R) ⟨t, h⟩ else 0)

omit [HasZeroObject C] [HasBinaryBiproducts C] in
@[reassoc]
theorem ι_restrFull_of_mem {S : Set T} (t : T) (h : t ∈ S) :
    Sigma.ι (fun _ : T => R) t ≫ restrFull R S = Sigma.ι (fun _ : S => R) ⟨t, h⟩ := by
  classical
  rw [restrFull, Sigma.ι_desc, dif_pos h]

omit [HasZeroObject C] [HasBinaryBiproducts C] in
@[reassoc]
theorem ι_restrFull_of_notMem {S : Set T} (t : T) (h : t ∉ S) :
    Sigma.ι (fun _ : T => R) t ≫ restrFull R S = 0 := by
  classical
  rw [restrFull, Sigma.ι_desc, dif_neg h]

section

variable (S₁ S₂ : Set T)

/-- The inclusion of the coproduct over the intersection into the biproduct. -/
noncomputable def mvFst : subCoproduct R (S₁ ∩ S₂) ⟶ subCoproduct R S₁ ⊞ subCoproduct R S₂ :=
  biprod.lift (inclCop R Set.inter_subset_left) (inclCop R Set.inter_subset_right)

/-- The difference of the two inclusions into the coproduct over the whole set. -/
noncomputable def mvSnd :
    subCoproduct R S₁ ⊞ subCoproduct R S₂ ⟶ ∐ (fun _ : T => R) :=
  biprod.desc (inclFull R S₁) (-inclFull R S₂)

omit [HasZeroObject C] in
theorem mvFst_comp_mvSnd : mvFst R S₁ S₂ ≫ mvSnd R S₁ S₂ = 0 := by
  refine Sigma.hom_ext _ _ (fun x => ?_)
  simp [mvFst, mvSnd, biprod.lift_desc]

/-- The Mayer--Vietoris short complex of coproducts. -/
noncomputable def coproductMVShortComplex : ShortComplex C :=
  ShortComplex.mk _ _ (mvFst_comp_mvSnd R S₁ S₂)

omit [HasZeroObject C] in
@[simp] theorem coproductMVShortComplex_f : (coproductMVShortComplex R S₁ S₂).f = mvFst R S₁ S₂ := rfl

omit [HasZeroObject C] in
@[simp] theorem coproductMVShortComplex_g : (coproductMVShortComplex R S₁ S₂).g = mvSnd R S₁ S₂ := rfl

/-- The retraction: project to the second summand and keep only the basis elements of the
intersection. -/
noncomputable def mvRetraction :
    subCoproduct R S₁ ⊞ subCoproduct R S₂ ⟶ subCoproduct R (S₁ ∩ S₂) :=
  biprod.snd ≫ restr R S₂ (S₁ ∩ S₂)

/-- The section: send a basis element to the first summand if it lies in the first subset, and to
minus the second summand otherwise. -/
noncomputable def mvSection :
    (∐ fun _ : T => R) ⟶ subCoproduct R S₁ ⊞ subCoproduct R S₂ :=
  restrFull R S₁ ≫ biprod.inl
    - restrFull R (S₂ \ S₁) ≫ inclCop R Set.sdiff_subset ≫ biprod.inr

omit [HasZeroObject C] in
theorem mvFst_comp_mvRetraction : mvFst R S₁ S₂ ≫ mvRetraction R S₁ S₂ = 𝟙 _ := by
  rw [mvFst, mvRetraction, ← Category.assoc, biprod.lift_snd]
  refine Sigma.hom_ext _ _ (fun x => ?_)
  rw [← Category.assoc, ι_inclCop,
    ι_restr_of_mem R (⟨(x : T), Set.inter_subset_right x.2⟩ : (S₂ : Set T)) x.2, Category.comp_id]

variable (hcover : S₁ ∪ S₂ = Set.univ)

include hcover

omit [HasZeroObject C] in
theorem mvSection_comp_mvSnd : mvSection R S₁ S₂ ≫ mvSnd R S₁ S₂ = 𝟙 _ := by
  refine Sigma.hom_ext _ _ (fun x => ?_)
  rw [Category.comp_id, mvSection, mvSnd, Preadditive.sub_comp, Preadditive.comp_sub]
  by_cases hx : (x : T) ∈ S₁
  · rw [Category.assoc, biprod.inl_desc, ι_restrFull_of_mem_assoc R x hx, ι_inclFull,
      Category.assoc, Category.assoc, biprod.inr_desc,
      ι_restrFull_of_notMem_assoc R x (by simp [hx]), Limits.zero_comp, sub_zero]
  · have hx2 : x ∈ S₂ \ S₁ := by
      refine ⟨?_, hx⟩
      have hmem := Set.eq_univ_iff_forall.1 hcover x
      exact Or.resolve_left hmem hx
    rw [Category.assoc, biprod.inl_desc, ι_restrFull_of_notMem_assoc R x hx, Limits.zero_comp,
      Category.assoc, Category.assoc, biprod.inr_desc, ι_restrFull_of_mem_assoc R x hx2,
      ι_inclCop_assoc, Preadditive.comp_neg, ι_inclFull, zero_sub, neg_neg]

omit [HasZeroObject C] hcover in
theorem mv_splitting_id :
    mvRetraction R S₁ S₂ ≫ mvFst R S₁ S₂ + mvSnd R S₁ S₂ ≫ mvSection R S₁ S₂ = 𝟙 _ := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [Preadditive.comp_add, Category.comp_id, mvRetraction, ← Category.assoc, ← Category.assoc,
      biprod.inl_snd, Limits.zero_comp, Limits.zero_comp, zero_add, mvSnd, ← Category.assoc,
      biprod.inl_desc]
    refine Sigma.hom_ext _ _ (fun x => ?_)
    rw [← Category.assoc, ι_inclFull, mvSection, Preadditive.comp_sub,
      ι_restrFull_of_mem_assoc R (x : T) x.2,
      ι_restrFull_of_notMem_assoc R (x : T) (by simp [x.2]), Limits.zero_comp, sub_zero]
  · rw [Preadditive.comp_add, Category.comp_id, mvRetraction, ← Category.assoc, ← Category.assoc,
      biprod.inr_snd, Category.id_comp, mvSnd, ← Category.assoc, biprod.inr_desc]
    refine Sigma.hom_ext _ _ (fun x => ?_)
    rw [Preadditive.comp_add, ← Category.assoc, Preadditive.neg_comp, Preadditive.comp_neg,
      ← Category.assoc, ι_inclFull, mvSection, Preadditive.comp_sub]
    rw [Category.assoc]
    by_cases hx : (x : T) ∈ S₁
    · rw [ι_restr_of_mem_assoc R x (⟨hx, x.2⟩ : (x : T) ∈ S₁ ∩ S₂), mvFst, biprod.lift_eq,
        Preadditive.comp_add, ι_inclCop_assoc, ι_inclCop_assoc,
        ι_restrFull_of_mem_assoc R (x : T) hx,
        ι_restrFull_of_notMem_assoc R (x : T) (by simp [hx]), Limits.zero_comp, sub_zero]
      abel
    · rw [ι_restr_of_notMem_assoc R x (by simp [hx]), Limits.zero_comp, zero_add,
        ι_restrFull_of_notMem_assoc R (x : T) hx, Limits.zero_comp, zero_sub,
        ι_restrFull_of_mem_assoc R (x : T) ((Set.mem_sdiff _).2 ⟨x.2, hx⟩), neg_neg,
        ι_inclCop_assoc]

/-- **The Mayer--Vietoris sequence of coproducts is split.** -/
noncomputable def mvSplitting : (coproductMVShortComplex R S₁ S₂).Splitting where
  r := mvRetraction R S₁ S₂
  s := mvSection R S₁ S₂
  f_r := mvFst_comp_mvRetraction R S₁ S₂
  s_g := mvSection_comp_mvSnd R S₁ S₂ hcover
  id := mv_splitting_id R S₁ S₂

/-- **And therefore short exact.** -/
theorem mvShortExact : (coproductMVShortComplex R S₁ S₂).ShortExact :=
  (mvSplitting R S₁ S₂ hcover).shortExact

end

end GaloisForLFunctions.HTGeometry
