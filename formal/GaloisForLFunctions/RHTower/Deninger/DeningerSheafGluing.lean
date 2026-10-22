import GaloisForLFunctions.RHTower.Deninger.DeningerFineSheaf

/-!
# Gluing, locally finite sums, and left exactness of sections

Three elementary facts about sheaves of abelian groups that the partition-of-unity argument needs.

Sections defined on a cover and agreeing on the overlaps glue, and a section is determined by its
restrictions to a cover.  A family of sections of which, near every point, all but finitely many
restrict to zero has a well defined sum: the finite partial sums agree on overlaps, so they glue.
And sections are left exact: a section of the middle term of a short exact sequence that dies in
the quotient comes from the subsheaf, because the free abelian sheaf on the open set corepresents
sections and the subsheaf is the kernel.

* `RHTower.deningerGlue`, `RHTower.deningerRes_ext` : gluing and its uniqueness.
* `RHTower.deningerLocallyFiniteSum` : the sum of a locally finite family of sections.
* `RHTower.deningerSections_exact` : left exactness of sections.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat

universe u

variable {X : TopCat.{u}}

section Restriction

variable {F : TopCat.Sheaf AddCommGrpCat.{u} X}

@[simp] theorem deningerRes_self (U : Opens X) (s : ToType (F.1.obj (op U))) :
    deningerRes F (le_refl U) s = s := by
  show ConcreteCategory.hom (F.1.map (homOfLE (le_refl U)).op) s = s
  rw [show (homOfLE (le_refl U)).op = 𝟙 (op U) from rfl, F.1.map_id]
  rfl

theorem deningerRes_res {U V W : Opens X} (h1 : V ≤ U) (h2 : W ≤ V)
    (s : ToType (F.1.obj (op U))) :
    deningerRes F h2 (deningerRes F h1 s) = deningerRes F (h2.trans h1) s := by
  show ConcreteCategory.hom (F.1.map (homOfLE h2).op)
      (ConcreteCategory.hom (F.1.map (homOfLE h1).op) s) = _
  rw [← ConcreteCategory.comp_apply, ← F.1.map_comp]
  rfl

theorem deningerRes_add {U W : Opens X} (h : W ≤ U) (s t : ToType (F.1.obj (op U))) :
    deningerRes F h (s + t) = deningerRes F h s + deningerRes F h t :=
  map_add _ s t

theorem deningerRes_sub {U W : Opens X} (h : W ≤ U) (s t : ToType (F.1.obj (op U))) :
    deningerRes F h (s - t) = deningerRes F h s - deningerRes F h t :=
  map_sub _ s t

theorem deningerRes_zero {U W : Opens X} (h : W ≤ U) :
    deningerRes F h (0 : ToType (F.1.obj (op U))) = 0 :=
  map_zero _

theorem deningerRes_sum {U W : Opens X} (h : W ≤ U) {ι : Type*} (S : Finset ι)
    (e : ι → ToType (F.1.obj (op U))) :
    deningerRes F h (∑ j ∈ S, e j) = ∑ j ∈ S, deningerRes F h (e j) :=
  map_sum (ConcreteCategory.hom (F.1.map (homOfLE h).op)) e S

end Restriction

section Gluing

variable {F : TopCat.Sheaf AddCommGrpCat.{u} X}

/-- **A section is determined by its restrictions to a cover.** -/
theorem deningerRes_ext {ι : Type*} {V : Opens X} {W : ι → Opens X} (hWV : ∀ i, W i ≤ V)
    (hcov : V ≤ ⨆ i, W i) (s t : ToType (F.1.obj (op V)))
    (h : ∀ i, deningerRes F (hWV i) s = deningerRes F (hWV i) t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' F W V (fun i => homOfLE (hWV i)) hcov s t h

/-- **Sections defined on a cover and agreeing on the overlaps glue.** -/
theorem deningerGlue {ι : Type*} {V : Opens X} {W : ι → Opens X} (hWV : ∀ i, W i ≤ V)
    (hcov : V ≤ ⨆ i, W i) (sf : ∀ i, ToType (F.1.obj (op (W i))))
    (hcomp : ∀ i j, deningerRes F (inf_le_left : W i ⊓ W j ≤ W i) (sf i)
      = deningerRes F (inf_le_right : W i ⊓ W j ≤ W j) (sf j)) :
    ∃ s : ToType (F.1.obj (op V)), ∀ i, deningerRes F (hWV i) s = sf i := by
  obtain ⟨s, hs, -⟩ :=
    TopCat.Sheaf.existsUnique_gluing' F W V (fun i => homOfLE (hWV i)) hcov sf hcomp
  exact ⟨s, hs⟩

/-- Compatibility on the intersection gives compatibility on every common refinement. -/
theorem deningerRes_of_overlap {W₁ W₂ Z : Opens X} (hi : Z ≤ W₁) (hj : Z ≤ W₂)
    (s₁ : ToType (F.1.obj (op W₁))) (s₂ : ToType (F.1.obj (op W₂)))
    (hc : deningerRes F (inf_le_left : W₁ ⊓ W₂ ≤ W₁) s₁
      = deningerRes F (inf_le_right : W₁ ⊓ W₂ ≤ W₂) s₂) :
    deningerRes F hi s₁ = deningerRes F hj s₂ := by
  have hZ : Z ≤ W₁ ⊓ W₂ := le_inf hi hj
  rw [← deningerRes_res (inf_le_left : W₁ ⊓ W₂ ≤ W₁) hZ s₁,
    ← deningerRes_res (inf_le_right : W₁ ⊓ W₂ ≤ W₂) hZ s₂, hc]

/-- Gluing with the compatibility stated on every common refinement. -/
theorem deningerGlue' {ι : Type*} {V : Opens X} {W : ι → Opens X} (hWV : ∀ i, W i ≤ V)
    (hcov : V ≤ ⨆ i, W i) (sf : ∀ i, ToType (F.1.obj (op (W i))))
    (hcomp : ∀ (i j : ι) (Z : Opens X) (hi : Z ≤ W i) (hj : Z ≤ W j),
      deningerRes F hi (sf i) = deningerRes F hj (sf j)) :
    ∃ s : ToType (F.1.obj (op V)), ∀ i, deningerRes F (hWV i) s = sf i :=
  deningerGlue hWV hcov sf fun i j => hcomp i j _ inf_le_left inf_le_right

/-- **A section is determined by its restrictions to a two-piece cover.** -/
theorem deningerRes_ext_two {V W₁ W₂ : Opens X} (h1 : W₁ ≤ V) (h2 : W₂ ≤ V) (hcov : V ≤ W₁ ⊔ W₂)
    (s t : ToType (F.1.obj (op V))) (e1 : deningerRes F h1 s = deningerRes F h1 t)
    (e2 : deningerRes F h2 s = deningerRes F h2 t) : s = t := by
  classical
  refine deningerRes_ext (F := F) (W := fun b : Bool => cond b W₁ W₂)
    (fun b => by cases b <;> assumption) ?_ s t ?_
  · rw [iSup_bool_eq]
    exact hcov
  · intro b
    cases b
    · exact e2
    · exact e1

/-- **Two sections on a two-piece cover agreeing on the overlap glue.** -/
theorem deningerGlue_two {V W₁ W₂ : Opens X} (h1 : W₁ ≤ V) (h2 : W₂ ≤ V) (hcov : V ≤ W₁ ⊔ W₂)
    (s₁ : ToType (F.1.obj (op W₁))) (s₂ : ToType (F.1.obj (op W₂)))
    (hc : deningerRes F (inf_le_left : W₁ ⊓ W₂ ≤ W₁) s₁
      = deningerRes F (inf_le_right : W₁ ⊓ W₂ ≤ W₂) s₂) :
    ∃ s : ToType (F.1.obj (op V)), deningerRes F h1 s = s₁ ∧ deningerRes F h2 s = s₂ := by
  classical
  set W : Bool → Opens X := fun b => cond b W₁ W₂ with hW
  have hWV : ∀ b, W b ≤ V := by
    intro b
    cases b
    · exact h2
    · exact h1
  have hcov' : V ≤ ⨆ b, W b := by
    rw [iSup_bool_eq]
    exact hcov
  refine (deningerGlue' hWV hcov' (fun b => Bool.rec s₂ s₁ b) ?_).imp fun s hs => ⟨hs true, hs false⟩
  intro b c Z hb hc'
  cases b <;> cases c
  · rfl
  · exact (deningerRes_of_overlap hc' hb s₁ s₂ hc).symm
  · exact deningerRes_of_overlap hb hc' s₁ s₂ hc
  · rfl

end Gluing

section LocallyFiniteSum

variable {F : TopCat.Sheaf AddCommGrpCat.{u} X}

/-- **A locally finite family of sections has a sum.**  The finite partial sums over the members of
a cover on which the family is finitely supported agree on the overlaps, so they glue; the resulting
section restricts to the finite partial sum on every open set where the family is finitely
supported. -/
theorem deningerLocallyFiniteSum {ι : Type*} {V : Opens X} (e : ι → ToType (F.1.obj (op V)))
    (hlf : ∀ x ∈ V, ∃ (W : Opens X) (hWV : W ≤ V), x ∈ W ∧
      ∃ S : Finset ι, ∀ j ∉ S, deningerRes F hWV (e j) = 0) :
    ∃ E : ToType (F.1.obj (op V)), ∀ (W : Opens X) (hWV : W ≤ V) (S : Finset ι),
      (∀ j ∉ S, deningerRes F hWV (e j) = 0) →
      deningerRes F hWV E = ∑ j ∈ S, deningerRes F hWV (e j) := by
  classical
  choose! W hWV hxW S hS using hlf
  set ι' := {x : X // x ∈ V} with hι'
  set W' : ι' → Opens X := fun x => W x.1 with hW'
  have hWV' : ∀ x : ι', W' x ≤ V := fun x => hWV x.1 x.2
  have hcov : V ≤ ⨆ x : ι', W' x := fun y hy =>
    Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxW y hy⟩
  -- the partial sums on the pieces of the cover
  set sf : ∀ x : ι', ToType (F.1.obj (op (W' x))) :=
    fun x => ∑ j ∈ S x.1, deningerRes F (hWV' x) (e j) with hsf
  -- a partial sum is unchanged by enlarging the index set with terms that vanish
  have hgrow : ∀ (Y : Opens X) (hYV : Y ≤ V) (S₁ S₂ : Finset ι),
      (∀ j ∉ S₁, deningerRes F hYV (e j) = 0) → S₁ ⊆ S₂ →
      ∑ j ∈ S₁, deningerRes F hYV (e j) = ∑ j ∈ S₂, deningerRes F hYV (e j) := by
    intro Y hYV S₁ S₂ hvan hsub
    exact Finset.sum_subset hsub fun j _ hj => hvan j hj
  have hcomp : ∀ x y : ι', deningerRes F (inf_le_left : W' x ⊓ W' y ≤ W' x) (sf x)
      = deningerRes F (inf_le_right : W' x ⊓ W' y ≤ W' y) (sf y) := by
    intro x y
    have hxle : W' x ⊓ W' y ≤ V := le_trans inf_le_left (hWV' x)
    have hex : deningerRes F (inf_le_left : W' x ⊓ W' y ≤ W' x) (sf x)
        = ∑ j ∈ S x.1, deningerRes F hxle (e j) := by
      rw [hsf]
      rw [deningerRes_sum]
      exact Finset.sum_congr rfl fun j _ => deningerRes_res _ _ _
    have hey : deningerRes F (inf_le_right : W' x ⊓ W' y ≤ W' y) (sf y)
        = ∑ j ∈ S y.1, deningerRes F hxle (e j) := by
      rw [hsf]
      rw [deningerRes_sum]
      exact Finset.sum_congr rfl fun j _ => deningerRes_res _ _ _
    have hvanx : ∀ j ∉ S x.1, deningerRes F hxle (e j) = 0 := by
      intro j hj
      rw [← deningerRes_res (hWV' x) (inf_le_left : W' x ⊓ W' y ≤ W' x) (e j),
        hS x.1 x.2 j hj, deningerRes_zero]
    have hvany : ∀ j ∉ S y.1, deningerRes F hxle (e j) = 0 := by
      intro j hj
      rw [← deningerRes_res (hWV' y) (inf_le_right : W' x ⊓ W' y ≤ W' y) (e j),
        hS y.1 y.2 j hj, deningerRes_zero]
    rw [hex, hey,
      hgrow _ hxle _ (S x.1 ∪ S y.1) hvanx Finset.subset_union_left,
      hgrow _ hxle _ (S x.1 ∪ S y.1) hvany Finset.subset_union_right]
  obtain ⟨E, hE⟩ := deningerGlue hWV' hcov sf hcomp
  refine ⟨E, fun Y hYV T hT => ?_⟩
  -- both sides restrict to the same thing on each piece of the cover
  have hcovY : Y ≤ ⨆ x : ι', Y ⊓ W' x := by
    intro y hy
    exact Opens.mem_iSup.2 ⟨⟨y, hYV hy⟩, ⟨hy, hxW y (hYV hy)⟩⟩
  refine deningerRes_ext (F := F) (fun x : ι' => (inf_le_left : Y ⊓ W' x ≤ Y)) hcovY _ _
    fun x => ?_
  have hle : Y ⊓ W' x ≤ V := le_trans inf_le_left hYV
  have hleft : deningerRes F (inf_le_left : Y ⊓ W' x ≤ Y) (deningerRes F hYV E)
      = ∑ j ∈ S x.1, deningerRes F hle (e j) := by
    rw [deningerRes_res, ← deningerRes_res (hWV' x) (inf_le_right : Y ⊓ W' x ≤ W' x) E,
      hE x, hsf, deningerRes_sum]
    exact Finset.sum_congr rfl fun j _ => deningerRes_res _ _ _
  have hright : deningerRes F (inf_le_left : Y ⊓ W' x ≤ Y)
      (∑ j ∈ T, deningerRes F hYV (e j)) = ∑ j ∈ T, deningerRes F hle (e j) := by
    rw [deningerRes_sum]
    exact Finset.sum_congr rfl fun j _ => deningerRes_res _ _ _
  have hvanx : ∀ j ∉ S x.1, deningerRes F hle (e j) = 0 := by
    intro j hj
    rw [← deningerRes_res (hWV' x) (inf_le_right : Y ⊓ W' x ≤ W' x) (e j),
      hS x.1 x.2 j hj, deningerRes_zero]
  have hvanT : ∀ j ∉ T, deningerRes F hle (e j) = 0 := by
    intro j hj
    rw [← deningerRes_res hYV (inf_le_left : Y ⊓ W' x ≤ Y) (e j), hT j hj, deningerRes_zero]
  rw [hleft, hright, hgrow _ hle _ (S x.1 ∪ T) hvanx Finset.subset_union_left,
    hgrow _ hle _ (S x.1 ∪ T) hvanT Finset.subset_union_right]

end LocallyFiniteSum

section LeftExact

/-- The corepresentation of sections sends the zero map to the zero section. -/
theorem deningerOpenFreeHomEquiv_zero (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    deningerOpenFreeHomEquiv U F 0 = 0 := by
  have h := deningerOpenFreeHomEquiv_naturality_right U (0 : F ⟶ F) (0 : deningerOpenFree U ⟶ F)
  rw [zero_comp] at h
  rw [h]
  exact map_zero _

/-- **Sections are left exact**: a section of the middle term of a short exact sequence of sheaves
that dies in the quotient comes from the subsheaf. -/
theorem deningerSections_exact {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (W : Opens X) (b : ToType (S.X₂.1.obj (op W)))
    (hb : ConcreteCategory.hom (S.g.1.app (op W)) b = 0) :
    ∃ a : ToType (S.X₁.1.obj (op W)), ConcreteCategory.hom (S.f.1.app (op W)) a = b := by
  haveI := hS.mono_f
  set β : deningerOpenFree W ⟶ S.X₂ := (deningerOpenFreeHomEquiv W S.X₂).symm b with hβ
  have hβb : deningerOpenFreeHomEquiv W S.X₂ β = b := by
    rw [hβ, Equiv.apply_symm_apply]
  have hβg : β ≫ S.g = 0 := by
    refine (deningerOpenFreeHomEquiv W S.X₃).injective ?_
    rw [deningerOpenFreeHomEquiv_naturality_right, hβb, hb,
      deningerOpenFreeHomEquiv_zero]
  refine ⟨deningerOpenFreeHomEquiv W S.X₁ (hS.exact.lift β hβg), ?_⟩
  rw [← deningerOpenFreeHomEquiv_naturality_right, hS.exact.lift_f, hβb]

end LeftExact

end RHTower
