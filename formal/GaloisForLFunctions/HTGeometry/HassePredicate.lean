import GaloisForLFunctions.HTGeometry.HasseFamily

/-!
# Predicate-level Hasse principles

`HassePredicate` records a global property equivalent to its validity at every place.  It supplies
the corresponding local obstruction theorem and structural operations for transporting, reindexing,
and combining local--global systems.  Every separating `HasseFamily` induces an equality predicate.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

/-- A global predicate whose truth is equivalent to truth at every local place. -/
structure HassePredicate (G : Type u) (ι : Type v) where
  global : G → Prop
  atPlace : ι → G → Prop
  local_global : ∀ x, global x ↔ ∀ i, atPlace i x

namespace HassePredicate

variable {G : Type u} {ι : Type v} (H : HassePredicate G ι)

/-- Package one fixed local--global equivalence as a Hasse predicate. -/
def fixed {P : Prop} {Q : ι → Prop} (h : P ↔ ∀ i, Q i) :
    HassePredicate Unit ι where
  global _ := P
  atPlace i _ := Q i
  local_global _ := h

/-- Failure of a global Hasse predicate is exactly failure at one place. -/
theorem not_global_iff_exists_local_not (x : G) :
    ¬ H.global x ↔ ∃ i, ¬ H.atPlace i x := by
  classical
  constructor
  · intro hglobal
    by_contra hlocal
    push Not at hlocal
    exact hglobal ((H.local_global x).mpr hlocal)
  · rintro ⟨i, hi⟩ hglobal
    exact hi ((H.local_global x).mp hglobal i)

/-- Pull a Hasse predicate back along a map of global objects. -/
def pullback {X : Type w} (f : X → G) : HassePredicate X ι where
  global x := H.global (f x)
  atPlace i x := H.atPlace i (f x)
  local_global x := H.local_global (f x)

/-- A surjective reindexing of places preserves a Hasse predicate. -/
def reindex {κ : Type w} (f : κ → ι) (hf : Function.Surjective f) :
    HassePredicate G κ where
  global := H.global
  atPlace k := H.atPlace (f k)
  local_global x := by
    constructor
    · intro hx k
      exact (H.local_global x).mp hx (f k)
    · intro hx
      apply (H.local_global x).mpr
      intro i
      obtain ⟨k, rfl⟩ := hf i
      exact hx k

/-- Conjunction combines two local--global systems over the disjoint union of their places. -/
def and {κ : Type w} (J : HassePredicate G κ) : HassePredicate G (Sum ι κ) where
  global x := H.global x ∧ J.global x
  atPlace i x := Sum.elim H.atPlace J.atPlace i x
  local_global x := by
    constructor
    · rintro ⟨hH, hJ⟩ i
      cases i with
      | inl i => exact (H.local_global x).mp hH i
      | inr i => exact (J.local_global x).mp hJ i
    · intro h
      constructor
      · apply (H.local_global x).mpr
        intro i
        exact h (Sum.inl i)
      · apply (J.local_global x).mpr
        intro i
        exact h (Sum.inr i)

end HassePredicate

/-- Logical dual of an existential local certificate: global failure means failure at every place.
This is the reusable contrapositive behind rigid faithfully-flat Hasse systems. -/
theorem not_iff_forall_not_of_iff_exists {ι : Type v} {P : Prop} {Q : ι → Prop}
    (h : P ↔ ∃ i, Q i) :
    ¬ P ↔ ∀ i, ¬ Q i := by
  have hn := not_congr h
  simpa only [not_exists] using hn

/-- A Hasse predicate for which one local place already certifies the global property.  Such
systems occur under faithfully flat descent: all places carry equivalent truth values, unlike a
genuine reciprocity obstruction that only vanishes after combining places. -/
structure RigidHassePredicate (G : Type u) (ι : Type v)
    extends HassePredicate G ι where
  global_exists : ∀ x, global x ↔ ∃ i, atPlace i x

namespace RigidHassePredicate

variable {G : Type u} {ι : Type v} (H : RigidHassePredicate G ι)

/-- In a rigid Hasse system, every individual place detects the global property. -/
theorem global_iff_atPlace (x : G) (i : ι) : H.global x ↔ H.atPlace i x := by
  constructor
  · intro hx
    exact (H.local_global x).mp hx i
  · intro hi
    exact (H.global_exists x).mpr ⟨i, hi⟩

/-- Any two places of a rigid Hasse system give equivalent local predicates. -/
theorem atPlace_iff_atPlace (x : G) (i j : ι) :
    H.atPlace i x ↔ H.atPlace j x :=
  (H.global_iff_atPlace x i).symm.trans (H.global_iff_atPlace x j)

/-- Global failure of a rigid Hasse predicate persists at every local place. -/
theorem not_global_iff_forall_local_not (x : G) :
    ¬ H.global x ↔ ∀ i, ¬ H.atPlace i x := by
  have h := not_congr (H.global_exists x)
  simpa only [not_exists] using h

end RigidHassePredicate

namespace HasseFamily

variable {G : Type u} {ι : Type v} (H : HasseFamily G ι)

/-- Every jointly separating observation family is a predicate-level Hasse principle for equality. -/
def equalityPredicate : HassePredicate (G × G) ι where
  global xy := xy.1 = xy.2
  atPlace i xy := H.profile xy.1 i = H.profile xy.2 i
  local_global xy := (H.pointwise_eq_iff xy.1 xy.2).symm

end HasseFamily

end GaloisForLFunctions.HTGeometry
