import GaloisForLFunctions.HTGeometry.FamilyIntervalCover
import GaloisForLFunctions.HTGeometry.LocallyConicalPoset

/-!
# The base of the family cover has no homology in positive degrees

In each component the elements that do not span the component's top with the component's atom fold
onto that atom by joining with it.  There is no global cone point — the atoms are different in
different components — but the fold is constant on comparable pairs, since comparable elements share
their component.  That is the locally conical situation.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Simplicial Opposite

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L] {ι : Type u} {W p : ι → L}

/-- Joining a non-spanning element with the atom of its component stays strictly below the top. -/
theorem base_join_lt (hpW : ∀ a, p a ≤ W a) {q : famBuilding W} (hq : q ∈ famCoverBase W p) :
    ((Subtype.val q).2 : L) ⊔ p (Subtype.val q).1 < W (Subtype.val q).1 :=
  lt_of_le_of_ne (sup_le (le_of_lt hq.1) (hpW _)) hq.2

/-- The atom of a component is itself a non-spanning element of that component. -/
theorem atom_mem_famCoverBase (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a)
    {q : famBuilding W} (hq : q ∈ famCoverBase W p) :
    (⟨((Subtype.val q).1,
        ⟨p (Subtype.val q).1, (hp _).1.bot_lt,
          lt_of_lt_of_le (lt_of_le_of_lt le_sup_right (base_join_lt hpW hq)) le_top⟩),
      lt_of_le_of_lt le_sup_right (base_join_lt hpW hq)⟩ : famBuilding W) ∈ famCoverBase W p := by
  refine ⟨lt_of_le_of_lt le_sup_right (base_join_lt hpW hq), ?_⟩
  show p (Subtype.val q).1 ⊔ p (Subtype.val q).1 ≠ W (Subtype.val q).1
  rw [sup_idem]
  exact ne_of_lt (lt_of_le_of_lt le_sup_right (base_join_lt hpW hq))

/-- The fold of the base onto the atoms, component by component. -/
def famBaseJoin (hpW : ∀ a, p a ≤ W a) :
    (famCoverBase W p : Type u) →o (famCoverBase W p : Type u) where
  toFun q :=
    ⟨⟨((Subtype.val (Subtype.val q)).1,
        ⟨((Subtype.val (Subtype.val q)).2 : L) ⊔ p (Subtype.val (Subtype.val q)).1,
          lt_of_lt_of_le (Subtype.val (Subtype.val q)).2.2.1 le_sup_left,
          lt_of_lt_of_le (base_join_lt hpW q.2) le_top⟩),
      base_join_lt hpW q.2⟩,
     ⟨base_join_lt hpW q.2, by
        show (((Subtype.val (Subtype.val q)).2 : L) ⊔ p (Subtype.val (Subtype.val q)).1)
          ⊔ p (Subtype.val (Subtype.val q)).1 ≠ W (Subtype.val (Subtype.val q)).1
        rw [sup_assoc, sup_idem]
        exact q.2.2⟩⟩
  monotone' q q' h := by
    obtain ⟨hidx, hle⟩ := famPoset_le_iff.1 h
    refine ⟨hidx, ?_⟩
    show ((Subtype.val (Subtype.val q)).2 : L) ⊔ p (Subtype.val (Subtype.val q)).1
      ≤ ((Subtype.val (Subtype.val q')).2 : L) ⊔ p (Subtype.val (Subtype.val q')).1
    rw [hidx]
    exact sup_le_sup_right hle _

/-- Sending every element of the base to the atom of its own component. -/
def famBaseCentre (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a) :
    (famCoverBase W p : Type u) →o (famCoverBase W p : Type u) where
  toFun q :=
    ⟨⟨((Subtype.val (Subtype.val q)).1,
        ⟨p (Subtype.val (Subtype.val q)).1, (hp _).1.bot_lt,
          lt_of_lt_of_le (lt_of_le_of_lt le_sup_right (base_join_lt hpW q.2)) le_top⟩),
      lt_of_le_of_lt le_sup_right (base_join_lt hpW q.2)⟩,
     atom_mem_famCoverBase hp hpW q.2⟩
  monotone' q q' h := by
    obtain ⟨hidx, -⟩ := famPoset_le_iff.1 h
    refine ⟨hidx, ?_⟩
    show p (Subtype.val (Subtype.val q)).1 ≤ p (Subtype.val (Subtype.val q')).1
    rw [hidx]

/-- **The base of the family cover has no homology in positive degrees.** -/
theorem isZero_homology_famCoverBase (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a)
    {C : Type*} [Category C] [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C]
    (R : C) (i : ℕ) (hi : 1 ≤ i) :
    Limits.IsZero
      (((nerveSubcomplex (famCoverBase W p) : (nerve (famBuilding W)).Subcomplex) :
        SSet.{u}).homology R i) := by
  refine Limits.IsZero.of_iso ?_ (nerveSubcomplexHomologyIso _ R i)
  refine isZero_homology_of_locally_conical (famBaseJoin hpW) (famBaseCentre hp hpW)
    (fun q => ?_) (fun q => ?_) (fun q q' h => ?_) R i hi
  · refine ⟨rfl, ?_⟩
    show ((Subtype.val (Subtype.val q)).2 : L)
      ≤ ((Subtype.val (Subtype.val q)).2 : L) ⊔ p (Subtype.val (Subtype.val q)).1
    exact le_sup_left
  · refine ⟨rfl, ?_⟩
    show p (Subtype.val (Subtype.val q)).1
      ≤ ((Subtype.val (Subtype.val q)).2 : L) ⊔ p (Subtype.val (Subtype.val q)).1
    exact le_sup_right
  · obtain ⟨hidx, -⟩ := famPoset_le_iff.1 h
    exact Subtype.ext (Subtype.ext (Prod.ext hidx (Subtype.ext (congrArg p hidx))))

end GaloisForLFunctions.HTGeometry
