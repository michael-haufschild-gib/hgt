import GaloisForLFunctions.HTGeometry.FamilyIntervalCover

/-!
# The family cover index is empty exactly when nothing spans

The complementary side of the cover laws asks for an *empty* index.  It is empty precisely when no
component has a proper part spanning it with the marked element, and two structural situations force
that: no components at all, and a lattice with no proper part — the two-element lattice, where the
only elements are the bottom and the top.
-/

namespace GaloisForLFunctions.HTGeometry

variable {L : Type u} [Lattice L] [BoundedOrder L] {ι : Type u} {W p : ι → L}

/-- **Nothing spanning makes the cover index empty.** -/
theorem isEmpty_famCoverIndex_of_forall_notMem
    (h : ∀ (i : ι) (U : properPart L), U ∉ spanningBelow (W i) (p i)) :
    IsEmpty (famCoverIndex W p) :=
  ⟨fun c => h c.1.1 c.1.2 c.2⟩

/-- With no components the cover index is empty. -/
theorem isEmpty_famCoverIndex_of_isEmpty [IsEmpty ι] : IsEmpty (famCoverIndex W p) :=
  isEmpty_famCoverIndex_of_forall_notMem fun i _ => (IsEmpty.false i).elim

/-- With no proper part the cover index is empty. -/
theorem isEmpty_famCoverIndex_of_isEmpty_properPart [IsEmpty (properPart L)] :
    IsEmpty (famCoverIndex W p) :=
  isEmpty_famCoverIndex_of_forall_notMem fun _ U => (IsEmpty.false U).elim

/-- The two-element lattice has no proper part. -/
instance : IsEmpty (properPart Bool) := by
  refine ⟨fun U => ?_⟩
  obtain ⟨u, hbot, htop⟩ := U
  cases u
  · exact absurd hbot (lt_irrefl _)
  · exact absurd htop (lt_irrefl _)

/-- **Over the two-element lattice the cover index is empty**, whatever the components. -/
theorem isEmpty_famCoverIndex_bool {ι : Type} {W p : ι → Bool} :
    IsEmpty (famCoverIndex W p) :=
  isEmpty_famCoverIndex_of_isEmpty_properPart

end GaloisForLFunctions.HTGeometry
