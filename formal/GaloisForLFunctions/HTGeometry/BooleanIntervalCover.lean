import GaloisForLFunctions.HTGeometry.PiZeroNerve
import GaloisForLFunctions.HTGeometry.FamilyBuildingFree
import Mathlib.Data.Set.Card

/-!
# The cover of a Boolean interval has exactly one piece

Inside the lattice of subsets, the elements of an interval `[∅, S]` that span it together with a
one-point subset `{a}` are exactly one: the complement of `a` in `S`.  So the Solomon--Tits cover of
a Boolean interval is a base together with a single star, and its descent goes from `S` to `S \ {a}`
without any branching — that is the thinness of a Coxeter complex, in the form the induction uses.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Simplicial Opposite

universe u

/-! ## Reindexing a disjoint union over a one-element index -/

section Reindex

variable {L : Type u} [Lattice L] [BoundedOrder L] {ι : Type u} [Unique ι] (W : ι → L)

/-- A disjoint union over a one-element index is the single interval building it consists of. -/
def famBuildingUniqueOrderIsoDefault :
    famBuilding W ≃o famBuilding (fun _ : PUnit.{u + 1} => W default) where
  toFun q := ⟨(PUnit.unit, (Subtype.val q).2), by
    have h : (Subtype.val q).1 = default := Unique.eq_default _
    have h2 : ((Subtype.val q).2 : properPart L) ∈ properBelow (W (Subtype.val q).1) := q.2
    rw [h] at h2
    exact h2⟩
  invFun q := ⟨(default, (Subtype.val q).2), q.2⟩
  left_inv q := Subtype.ext (Prod.ext (Unique.eq_default _).symm rfl)
  right_inv q := Subtype.ext (Prod.ext (Subsingleton.elim _ _) rfl)
  map_rel_iff' {q q'} := by
    constructor
    · intro h
      exact famPoset_le_iff.2 ⟨Subsingleton.elim _ _, (famPoset_le_iff.1 h).2⟩
    · intro h
      exact famPoset_le_iff.2 ⟨rfl, (famPoset_le_iff.1 h).2⟩

/-- The same, with the single interval named. -/
def famBuildingUniqueOrderIso (T : L) (hT : W default = T) :
    famBuilding W ≃o famBuilding (fun _ : PUnit.{u + 1} => T) := by
  subst hT
  exact famBuildingUniqueOrderIsoDefault W

end Reindex

/-! ## The cover of a Boolean interval -/

section Boolean

variable {ι : Type u} {S : Set ι} {a : ι}

theorem nonempty_sdiff_singleton (ha : a ∈ S) (h2 : 2 ≤ S.ncard) :
    (S \ {a}).Nonempty := by
  refine Set.nonempty_of_ncard_ne_zero ?_
  rw [Set.ncard_sdiff_singleton_of_mem ha]
  omega

/-- The complement of a point of an interval is a nonzero proper subset. -/
theorem sdiff_singleton_mem_properPart (ha : a ∈ S) (h2 : 2 ≤ S.ncard) :
    (⊥ : Set ι) < S \ {a} ∧ S \ {a} < ⊤ := by
  refine ⟨Set.empty_ssubset.2 (nonempty_sdiff_singleton ha h2), ?_⟩
  refine Set.ssubset_univ_iff.2 fun hcon => ?_
  have : a ∈ S \ {a} := by rw [hcon]; trivial
  exact this.2 rfl

/-- **The unique piece of the cover of a Boolean interval.** -/
def boolCoverElt (ha : a ∈ S) (h2 : 2 ≤ S.ncard) :
    famCoverIndex (fun _ : PUnit.{u + 1} => S) (fun _ => {a}) :=
  ⟨(PUnit.unit, ⟨S \ {a}, sdiff_singleton_mem_properPart ha h2⟩),
    Set.sdiff_singleton_ssubset.2 ha, Set.sdiff_union_of_subset (Set.singleton_subset_iff.2 ha)⟩

/-- **A spanning element of a Boolean interval is the complement of the atom.** -/
theorem boolCoverIndex_eq (ha : a ∈ S) (h2 : 2 ≤ S.ncard)
    (c : famCoverIndex (fun _ : PUnit.{u + 1} => S) (fun _ => {a})) :
    c = boolCoverElt ha h2 := by
  refine Subtype.ext (Prod.ext (Subsingleton.elim _ _) (Subtype.ext ?_))
  have hlt : ((Subtype.val c).2 : Set ι) < S := c.2.1
  have hsup : ((Subtype.val c).2 : Set ι) ∪ {a} = S := c.2.2
  have haU : a ∉ ((Subtype.val c).2 : Set ι) := by
    intro hcon
    have hself : ((Subtype.val c).2 : Set ι) ∪ {a} = ((Subtype.val c).2 : Set ι) :=
      Set.union_eq_self_of_subset_right (Set.singleton_subset_iff.2 hcon)
    exact absurd (hself.symm.trans hsup) (ne_of_lt hlt)
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · refine ⟨?_, fun hxa => haU (hxa ▸ hx)⟩
    rw [← hsup]
    exact Or.inl hx
  · have hxS : x ∈ ((Subtype.val c).2 : Set ι) ∪ {a} := by rw [hsup]; exact hx.1
    exact hxS.resolve_right hx.2

/-- **The cover of a Boolean interval has exactly one piece.** -/
@[reducible] def uniqueBoolCoverIndex (ha : a ∈ S) (h2 : 2 ≤ S.ncard) :
    Unique (famCoverIndex (fun _ : PUnit.{u + 1} => S) (fun _ => {a})) where
  default := boolCoverElt ha h2
  uniq := boolCoverIndex_eq ha h2

theorem famCoverTop_boolCoverElt (ha : a ∈ S) (h2 : 2 ≤ S.ncard) :
    famCoverTop (boolCoverElt ha h2) = S \ {a} := rfl

end Boolean

end GaloisForLFunctions.HTGeometry
