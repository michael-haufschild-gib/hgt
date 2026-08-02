import GaloisForLFunctions.HTGeometry.FamilyDegreeOneFree
import GaloisForLFunctions.HTGeometry.FamilyBuildingStep

/-!
# The components of the base of a family cover

Inside the base of the cover of a disjoint union of interval buildings, every element is joined to
the atom of its own component by two comparabilities: it is below its join with that atom, and so is
the atom.  So the component of the base in which an element sits is determined by the component of
the disjoint union it belongs to, and in particular by the piece that contains it.

This is the input the Mayer--Vietoris freeness argument needs in degree one: the map from the
intersections into the base factors through the map into the pieces.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u

/-! ## Vertices of a full subcomplex -/

section Vertices

variable {P : Type u} [PartialOrder P]

/-- The vertex of a full subcomplex attached to an element of the subset. -/
def nerveSubcomplexVertex {Q : Set P} (a : P) (ha : a ∈ Q) :
    ((nerveSubcomplex Q : (nerve P).Subcomplex) : SSet.{u}) _⦋0⦌ :=
  ⟨ComposableArrows.mk₀ a, fun _ => ha⟩

theorem nerveSubcomplexVertex_eq {Q : Set P}
    (y : ((nerveSubcomplex Q : (nerve P).Subcomplex) : SSet.{u}) _⦋0⦌) :
    y = nerveSubcomplexVertex ((y : (nerve P) _⦋0⦌).obj 0) (y.2 0) :=
  Subtype.ext (ComposableArrows.ext₀ rfl)

/-- **Comparable elements of the subset lie in the same component of the full subcomplex.** -/
theorem pi0_nerveSubcomplexVertex_eq_of_le {Q : Set P} {a b : P} (ha : a ∈ Q) (hb : b ∈ Q)
    (h : a ≤ b) :
    SSet.π₀.mk (nerveSubcomplexVertex a ha) = SSet.π₀.mk (nerveSubcomplexVertex b hb) :=
  SSet.π₀.sound ⟨⟨ComposableArrows.mk₁ (homOfLE h), by
      intro i
      fin_cases i
      · exact ha
      · exact hb⟩,
    Subtype.ext (ComposableArrows.ext₀ rfl), Subtype.ext (ComposableArrows.ext₀ rfl)⟩

end Vertices

/-! ## The index of a component of a disjoint union -/

section Index

variable {X : SSet.{u}} {ι : Type u} {A : ι → X.Subcomplex}

/-- The two ends of an edge of a disjoint union lie in the same member. -/
theorem famSSet_edge_index {x₀ x₁ : (famSSet A) _⦋0⦌} (e : SSet.Edge x₀ x₁) : x₀.1 = x₁.1 := by
  have h0 : (e.edge).1 = x₀.1 := congrArg Sigma.fst e.src_eq
  have h1 : (e.edge).1 = x₁.1 := congrArg Sigma.fst e.tgt_eq
  exact h0.symm.trans h1

/-- A function of the index of a disjoint union descends to its components. -/
def famSSetPi0Lift {T : Type u} (f : ι → T) : SSet.π₀ (famSSet A) → T :=
  SSet.π₀.lift (fun v => f v.1) (fun _ _ e => congrArg f (famSSet_edge_index e))

@[simp] theorem famSSetPi0Lift_mk {T : Type u} (f : ι → T) (v : (famSSet A) _⦋0⦌) :
    famSSetPi0Lift f (SSet.π₀.mk v) = f v.1 := rfl

end Index

/-! ## The atom of a component, inside the base -/

section

variable {L : Type u} [Lattice L] [BoundedOrder L] {ι : Type u} {W p : ι → L}

/-- The atom of a component that carries a piece is strictly below the top of that component. -/
theorem atom_lt_of_famCoverIndex (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a)
    (c : famCoverIndex W p) : p (Subtype.val c).1 < W (Subtype.val c).1 := by
  refine lt_of_le_of_ne (hpW _) fun heq => ?_
  have hlt : ((Subtype.val c).2 : L) < W (Subtype.val c).1 := c.2.1
  rw [← heq] at hlt
  exact absurd ((hp _).lt_iff.1 hlt) (ne_of_gt (Subtype.val c).2.2.1)

/-- The atom of the component of a piece, as an element of the disjoint union. -/
def famCoverAtomElt (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a) (c : famCoverIndex W p) :
    famBuilding W :=
  ⟨((Subtype.val c).1,
      ⟨p (Subtype.val c).1, (hp _).1.bot_lt,
        lt_of_lt_of_le (atom_lt_of_famCoverIndex hp hpW c) le_top⟩),
    atom_lt_of_famCoverIndex hp hpW c⟩

theorem famCoverAtomElt_mem_base (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a)
    (c : famCoverIndex W p) : famCoverAtomElt hp hpW c ∈ famCoverBase W p := by
  refine ⟨atom_lt_of_famCoverIndex hp hpW c, ?_⟩
  show p (Subtype.val c).1 ⊔ p (Subtype.val c).1 ≠ W (Subtype.val c).1
  rw [sup_idem]
  exact ne_of_lt (atom_lt_of_famCoverIndex hp hpW c)

/-- **Inside the base, every element is joined to the atom of its own component.** -/
theorem pi0_base_eq_atom (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a) (c : famCoverIndex W p)
    {q : famBuilding W} (hq : q ∈ famCoverBase W p)
    (hidx : (Subtype.val q).1 = (Subtype.val c).1) :
    SSet.π₀.mk (nerveSubcomplexVertex q hq)
      = SSet.π₀.mk (nerveSubcomplexVertex (famCoverAtomElt hp hpW c)
          (famCoverAtomElt_mem_base hp hpW c)) := by
  have hjoinmem : (Subtype.val (famBaseJoin hpW ⟨q, hq⟩)) ∈ famCoverBase W p :=
    (famBaseJoin hpW ⟨q, hq⟩).2
  have hq_le : q ≤ (Subtype.val (famBaseJoin hpW ⟨q, hq⟩)) := famPoset_le_iff.2 ⟨rfl, le_sup_left⟩
  have hatom_le : famCoverAtomElt hp hpW c ≤ (Subtype.val (famBaseJoin hpW ⟨q, hq⟩)) := by
    refine famPoset_le_iff.2 ⟨hidx.symm, ?_⟩
    show p (Subtype.val c).1 ≤ ((Subtype.val q).2 : L) ⊔ p (Subtype.val q).1
    rw [← hidx]
    exact le_sup_right
  refine (pi0_nerveSubcomplexVertex_eq_of_le hq hjoinmem hq_le).trans ?_
  exact (pi0_nerveSubcomplexVertex_eq_of_le (famCoverAtomElt_mem_base hp hpW c) hjoinmem
    hatom_le).symm

end

end GaloisForLFunctions.HTGeometry
