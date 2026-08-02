import GaloisForLFunctions.HTGeometry.CoproductMayerVietorisSup

/-!
# Mayer--Vietoris for a base together with an arbitrary family of pieces

A set `W` covered by a base `S₀` and a family `S a` whose members meet each other only inside the
base gives a split short exact sequence

```text
0 → ∐_{a} ∐_{S₀ ∩ S a} R → (∐_{S₀} R) ⊞ ∐_{a} ∐_{S a} R → ∐_{W} R → 0,
```

with no finiteness assumption on the index.  The reason it is exact for any index is that the pieces
are disjoint outside the base: an element of `W` lies in the base, or in exactly one piece.

This is what a cover with infinitely many pieces needs.  Folding a cover two pieces at a time proves
the statement for every finite partial union and stops there; the sequence above attaches all the
pieces at once.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [HasCoproducts.{w} C]

variable {T : Type w} {ι : Type w} (R : C) (S₀ : Set T) (S : ι → Set T)

/-- The disjoint union of the pieces. -/
abbrev famIndex : Type w := Σ a : ι, (S a : Type w)

/-- The disjoint union of the intersections of the pieces with the base. -/
abbrev famInterIndex : Type w := Σ a : ι, ((S₀ ∩ S a : Set T) : Type w)

/-- The coproduct over the disjoint union of the pieces. -/
noncomputable abbrev famCoproduct : C := ∐ (fun _ : famIndex S => R)

/-- The coproduct over the disjoint union of the intersections with the base. -/
noncomputable abbrev famInterCoproduct : C := ∐ (fun _ : famInterIndex S₀ S => R)

/-- The inclusion of the intersections into the base. -/
noncomputable def famBaseIncl : famInterCoproduct R S₀ S ⟶ subCoproduct R S₀ :=
  Sigma.desc (fun p => Sigma.ι (fun _ : (S₀ : Type w) => R) ⟨(p.2 : T), p.2.2.1⟩)

/-- The inclusion of the intersections into the disjoint union of the pieces. -/
noncomputable def famPieceIncl : famInterCoproduct R S₀ S ⟶ famCoproduct R S :=
  Sigma.desc (fun p => Sigma.ι (fun _ : famIndex S => R) ⟨p.1, ⟨(p.2 : T), p.2.2.2⟩⟩)

/-- The inclusion of the intersections into the biproduct. -/
noncomputable def famFst :
    famInterCoproduct R S₀ S ⟶ subCoproduct R S₀ ⊞ famCoproduct R S :=
  biprod.lift (famBaseIncl R S₀ S) (famPieceIncl R S₀ S)

open scoped Classical in
/-- Keep the basis elements of a piece that lie in the base. -/
noncomputable def famTrunc : famCoproduct R S ⟶ famInterCoproduct R S₀ S :=
  Sigma.desc (fun q : famIndex S =>
    if h : (q.2 : T) ∈ S₀ then
      Sigma.ι (fun _ : famInterIndex S₀ S => R) ⟨q.1, ⟨(q.2 : T), Set.mem_inter h q.2.2⟩⟩
    else 0)

omit [HasZeroObject C] [HasBinaryBiproducts C] in
@[reassoc]
theorem ι_famTrunc_of_mem (q : famIndex S) (h : (q.2 : T) ∈ S₀) :
    Sigma.ι (fun _ : famIndex S => R) q ≫ famTrunc R S₀ S
      = Sigma.ι (fun _ : famInterIndex S₀ S => R)
        ⟨q.1, ⟨(q.2 : T), Set.mem_inter h q.2.2⟩⟩ := by
  classical
  rw [famTrunc, Sigma.ι_desc, dif_pos h]

omit [HasZeroObject C] [HasBinaryBiproducts C] in
@[reassoc]
theorem ι_famTrunc_of_notMem (q : famIndex S) (h : (q.2 : T) ∉ S₀) :
    Sigma.ι (fun _ : famIndex S => R) q ≫ famTrunc R S₀ S = 0 := by
  classical
  rw [famTrunc, Sigma.ι_desc, dif_neg h]

/-- The retraction: project to the family and keep what lies in the base. -/
noncomputable def famRetraction :
    subCoproduct R S₀ ⊞ famCoproduct R S ⟶ famInterCoproduct R S₀ S :=
  biprod.snd ≫ famTrunc R S₀ S

omit [HasZeroObject C] in
theorem famFst_comp_famRetraction : famFst R S₀ S ≫ famRetraction R S₀ S = 𝟙 _ := by
  refine Sigma.hom_ext _ _ (fun p => ?_)
  rw [famFst, famRetraction, biprod.lift_snd_assoc, famPieceIncl,
    Sigma.ι_desc_assoc, ι_famTrunc_of_mem R S₀ S ⟨p.1, ⟨(p.2 : T), p.2.2.2⟩⟩ p.2.2.1,
    Category.comp_id]

/-- The inclusion of the disjoint union of the pieces into the coproduct over the covered set. -/
noncomputable def famIncl (W : Set T) (hpiece : ∀ a, S a ⊆ W) :
    famCoproduct R S ⟶ subCoproduct R W :=
  Sigma.desc (fun q : famIndex S =>
    Sigma.ι (fun _ : (W : Type w) => R) ⟨(q.2 : T), hpiece q.1 q.2.2⟩)

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem ι_famIncl (W : Set T) (hpiece : ∀ a, S a ⊆ W) (q : famIndex S) :
    Sigma.ι (fun _ : famIndex S => R) q ≫ famIncl R S W hpiece
      = Sigma.ι (fun _ : (W : Type w) => R) ⟨(q.2 : T), hpiece q.1 q.2.2⟩ :=
  Sigma.ι_desc _ _

/-- The difference of the two inclusions into the coproduct over the covered set. -/
noncomputable def famSnd (W : Set T) (hbase : S₀ ⊆ W) (hpiece : ∀ a, S a ⊆ W) :
    subCoproduct R S₀ ⊞ famCoproduct R S ⟶ subCoproduct R W :=
  biprod.desc (inclCop R hbase) (-famIncl R S W hpiece)

omit [HasZeroObject C] in
theorem famFst_comp_famSnd (W : Set T) (hbase : S₀ ⊆ W) (hpiece : ∀ a, S a ⊆ W) :
    famFst R S₀ S ≫ famSnd R S₀ S W hbase hpiece = 0 := by
  refine Sigma.hom_ext _ _ (fun p => ?_)
  rw [famFst, famSnd, biprod.lift_desc, Preadditive.comp_neg, famBaseIncl, famPieceIncl,
    Preadditive.comp_add, Preadditive.comp_neg, Sigma.ι_desc_assoc, Sigma.ι_desc_assoc,
    ι_inclCop, ι_famIncl, Limits.comp_zero]
  exact add_neg_cancel _

/-- The Mayer--Vietoris short complex of a base and a family. -/
noncomputable def famShortComplex (W : Set T) (hbase : S₀ ⊆ W) (hpiece : ∀ a, S a ⊆ W) :
    ShortComplex C :=
  ShortComplex.mk _ _ (famFst_comp_famSnd R S₀ S W hbase hpiece)

omit [HasZeroObject C] in
@[simp] theorem famShortComplex_f (W : Set T) (hbase : S₀ ⊆ W) (hpiece : ∀ a, S a ⊆ W) :
    (famShortComplex R S₀ S W hbase hpiece).f = famFst R S₀ S := rfl

omit [HasZeroObject C] in
@[simp] theorem famShortComplex_g (W : Set T) (hbase : S₀ ⊆ W) (hpiece : ∀ a, S a ⊆ W) :
    (famShortComplex R S₀ S W hbase hpiece).g = famSnd R S₀ S W hbase hpiece := rfl

open scoped Classical in
/-- The section: send a basis element of the base to the first summand, and any other basis element
to minus the summand of the piece that contains it. -/
noncomputable def famSection (W : Set T) (idx : T → ι)
    (hidx : ∀ x : (W : Set T), (x : T) ∉ S₀ → (x : T) ∈ S (idx x)) :
    subCoproduct R W ⟶ subCoproduct R S₀ ⊞ famCoproduct R S :=
  Sigma.desc (fun x =>
    if h : (x : T) ∈ S₀ then
      Sigma.ι (fun _ : (S₀ : Type w) => R) ⟨(x : T), h⟩ ≫ biprod.inl
    else
      -(Sigma.ι (fun _ : famIndex S => R) ⟨idx (x : T), ⟨(x : T), hidx x h⟩⟩ ≫ biprod.inr))

section

variable (W : Set T) (idx : T → ι)
  (hidx : ∀ x : (W : Set T), (x : T) ∉ S₀ → (x : T) ∈ S (idx x))

omit [HasZeroObject C] in
@[reassoc]
theorem ι_famSection_of_mem (x : (W : Set T)) (h : (x : T) ∈ S₀) :
    Sigma.ι (fun _ : (W : Type w) => R) x ≫ famSection R S₀ S W idx hidx
      = Sigma.ι (fun _ : (S₀ : Type w) => R) ⟨(x : T), h⟩ ≫ biprod.inl := by
  classical
  rw [famSection, Sigma.ι_desc, dif_pos h]

omit [HasZeroObject C] in
@[reassoc]
theorem ι_famSection_of_notMem (x : (W : Set T)) (h : (x : T) ∉ S₀) (a : ι)
    (hx : (x : T) ∈ S a) (ha : idx (x : T) = a) :
    Sigma.ι (fun _ : (W : Type w) => R) x ≫ famSection R S₀ S W idx hidx
      = -(Sigma.ι (fun _ : famIndex S => R) ⟨a, ⟨(x : T), hx⟩⟩ ≫ biprod.inr) := by
  classical
  subst ha
  rw [famSection, Sigma.ι_desc, dif_neg h]

omit [HasZeroObject C] in
theorem famSection_comp_famSnd (hbase : S₀ ⊆ W) (hpiece : ∀ a, S a ⊆ W) :
    famSection R S₀ S W idx hidx ≫ famSnd R S₀ S W hbase hpiece = 𝟙 _ := by
  refine Sigma.hom_ext _ _ (fun x => ?_)
  rw [Category.comp_id, ← Category.assoc]
  by_cases h : (x : T) ∈ S₀
  · rw [ι_famSection_of_mem R S₀ S W idx hidx x h, Category.assoc, famSnd, biprod.inl_desc,
      ι_inclCop]
  · rw [ι_famSection_of_notMem R S₀ S W idx hidx x h (idx (x : T)) (hidx x h) rfl,
      Preadditive.neg_comp, Category.assoc, famSnd, biprod.inr_desc, Preadditive.comp_neg,
      ι_famIncl, neg_neg]

omit [HasZeroObject C] in
/-- Outside the base a piece is determined by any of its elements. -/
theorem idx_eq_of_notMem (hdisj : ∀ a b : ι, a ≠ b → S a ∩ S b ⊆ S₀)
    (a : ι) (x : T) (hxa : x ∈ S a) (hx : x ∉ S₀) (hxi : x ∈ S (idx x)) : idx x = a := by
  by_contra hne
  exact hx (hdisj (idx x) a hne ⟨hxi, hxa⟩)

omit [HasZeroObject C] in
theorem fam_splitting_id (hbase : S₀ ⊆ W) (hpiece : ∀ a, S a ⊆ W)
    (hdisj : ∀ a b : ι, a ≠ b → S a ∩ S b ⊆ S₀) :
    famRetraction R S₀ S ≫ famFst R S₀ S
      + famSnd R S₀ S W hbase hpiece ≫ famSection R S₀ S W idx hidx = 𝟙 _ := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [Preadditive.comp_add, Category.comp_id, famRetraction, ← Category.assoc, ← Category.assoc,
      biprod.inl_snd, Limits.zero_comp, Limits.zero_comp, zero_add, famSnd, ← Category.assoc,
      biprod.inl_desc]
    refine Sigma.hom_ext _ _ (fun y => ?_)
    rw [← Category.assoc, ι_inclCop]
    exact ι_famSection_of_mem R S₀ S W idx hidx ⟨(y : T), hbase y.2⟩ y.2
  · rw [Preadditive.comp_add, Category.comp_id, famRetraction, ← Category.assoc, ← Category.assoc,
      biprod.inr_snd, Category.id_comp, famSnd, ← Category.assoc, biprod.inr_desc,
      Preadditive.neg_comp]
    refine Sigma.hom_ext _ _ (fun q => ?_)
    rw [Preadditive.comp_add, Preadditive.comp_neg]
    by_cases h : (q.2 : T) ∈ S₀
    · rw [ι_famTrunc_of_mem_assoc R S₀ S q h, famFst, biprod.lift_eq,
        ι_famIncl_assoc,
        ι_famSection_of_mem R S₀ S W idx hidx ⟨(q.2 : T), hpiece q.1 q.2.2⟩ h,
        Preadditive.comp_add, famBaseIncl, famPieceIncl, Sigma.ι_desc_assoc, Sigma.ι_desc_assoc]
      abel
    · rw [ι_famTrunc_of_notMem_assoc R S₀ S q h, Limits.zero_comp, zero_add, ι_famIncl_assoc,
        ι_famSection_of_notMem R S₀ S W idx hidx ⟨(q.2 : T), hpiece q.1 q.2.2⟩ h q.1 q.2.2
          (idx_eq_of_notMem S₀ S idx hdisj q.1 (q.2 : T) q.2.2 h
            (hidx ⟨(q.2 : T), hpiece q.1 q.2.2⟩ h)),
        neg_neg]

/-- **The Mayer--Vietoris sequence of a base and a family is split.** -/
noncomputable def famSplitting (idx' : T → ι)
    (hidx' : ∀ x : (W : Set T), (x : T) ∉ S₀ → (x : T) ∈ S (idx' x))
    (hbase : S₀ ⊆ W) (hpiece : ∀ a, S a ⊆ W)
    (hdisj : ∀ a b : ι, a ≠ b → S a ∩ S b ⊆ S₀) :
    (famShortComplex R S₀ S W hbase hpiece).Splitting where
  r := famRetraction R S₀ S
  s := famSection R S₀ S W idx' hidx'
  f_r := famFst_comp_famRetraction R S₀ S
  s_g := famSection_comp_famSnd R S₀ S W idx' hidx' hbase hpiece
  id := fam_splitting_id R S₀ S W idx' hidx' hbase hpiece hdisj

/-- **And therefore short exact.** -/
theorem famShortExact (idx' : T → ι)
    (hidx' : ∀ x : (W : Set T), (x : T) ∉ S₀ → (x : T) ∈ S (idx' x))
    (hbase : S₀ ⊆ W) (hpiece : ∀ a, S a ⊆ W)
    (hdisj : ∀ a b : ι, a ≠ b → S a ∩ S b ⊆ S₀) :
    (famShortComplex R S₀ S W hbase hpiece).ShortExact :=
  (famSplitting R S₀ S W idx' hidx' hbase hpiece hdisj).shortExact

end

/-- An index function choosing, for each element outside the base, a piece containing it. -/
theorem exists_idx [Nonempty ι] (W : Set T) (hcover : ∀ x ∈ W, x ∈ S₀ ∨ ∃ a, x ∈ S a) :
    ∃ idx : T → ι, ∀ x : (W : Set T), (x : T) ∉ S₀ → (x : T) ∈ S (idx x) := by
  classical
  refine ⟨fun x => if h : ∃ a, x ∈ S a then h.choose else Classical.arbitrary ι, ?_⟩
  intro x hx
  have hex : ∃ a, (x : T) ∈ S a := (hcover (x : T) x.2).resolve_left hx
  simpa only [dif_pos hex] using hex.choose_spec

/-- **The Mayer--Vietoris sequence of a base and a family, with the index chosen.** -/
theorem famShortExact' [Nonempty ι] (W : Set T) (hbase : S₀ ⊆ W) (hpiece : ∀ a, S a ⊆ W)
    (hcover : ∀ x ∈ W, x ∈ S₀ ∨ ∃ a, x ∈ S a)
    (hdisj : ∀ a b : ι, a ≠ b → S a ∩ S b ⊆ S₀) :
    (famShortComplex R S₀ S W hbase hpiece).ShortExact := by
  obtain ⟨idx, hidx⟩ := exists_idx S₀ S W hcover
  exact famShortExact R S₀ S W idx hidx hbase hpiece hdisj

end GaloisForLFunctions.HTGeometry
