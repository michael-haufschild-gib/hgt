import GaloisForLFunctions.HTGeometry.FamilyIntervalCover

/-!
# The family cover index is inhabited

The pieces of a family interval cover are indexed by a component together with a proper part that
spans it with the marked element.  The index type is nonempty exactly when some component admits
such a spanning part, and that happens in every lattice with a complemented proper part: in the
Boolean lattice on two points the complement of a marked atom spans with it.

So the cover laws are not statements about an empty index.
-/

namespace GaloisForLFunctions.HTGeometry

variable {L : Type u} [Lattice L] [BoundedOrder L] {ι : Type u} {W p : ι → L}

/-- **A spanning proper part of some component inhabits the cover index.** -/
theorem nonempty_famCoverIndex_of_mem {i : ι} {U : properPart L}
    (hU : U ∈ spanningBelow (W i) (p i)) : Nonempty (famCoverIndex W p) :=
  ⟨⟨(i, U), hU⟩⟩

/-- Conversely, an inhabited cover index exhibits such a component and part. -/
theorem exists_mem_spanningBelow_of_nonempty (h : Nonempty (famCoverIndex W p)) :
    ∃ (i : ι) (U : properPart L), U ∈ spanningBelow (W i) (p i) := by
  obtain ⟨⟨⟨i, U⟩, hU⟩⟩ := h
  exact ⟨i, U, hU⟩

/-! ## A concrete inhabited cover -/

/-- The two-point Boolean lattice, with the full component and one marked atom. -/
theorem nonempty_famCoverIndex_boolean :
    Nonempty (famCoverIndex (L := Set (Fin 2)) (ι := Unit)
      (fun _ => Set.univ) (fun _ => {0})) := by
  have hone : (⊥ : Set (Fin 2)) < {1} := by
    refine lt_of_le_of_ne bot_le ?_
    intro h
    have : (1 : Fin 2) ∈ ({1} : Set (Fin 2)) := rfl
    rw [← h] at this
    exact this
  have hlt : ({1} : Set (Fin 2)) < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro h
    have h0 : (0 : Fin 2) ∈ ({1} : Set (Fin 2)) := by rw [h]; trivial
    have h01 : (0 : Fin 2) = 1 := h0
    exact absurd (congrArg Fin.val h01) (by simp)
  refine nonempty_famCoverIndex_of_mem (i := ()) (U := ⟨{1}, hone, hlt⟩) ?_
  refine ⟨hlt, ?_⟩
  ext x
  fin_cases x <;> simp

end GaloisForLFunctions.HTGeometry
