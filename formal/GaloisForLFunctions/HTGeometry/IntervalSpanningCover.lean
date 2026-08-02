import GaloisForLFunctions.HTGeometry.BuildingSpanningCover

/-!
# The cover of the building of an interval

The cover of the previous module, relative to an element `V` rather than to the top: the proper part
of the interval below `V`, an atom `p ≤ V`, the elements below `V` that do not span it with `p`, and
the elements that do.  Those are exactly the coatoms of the interval, the pieces meet only inside
the base, and the base meets a piece in the proper part of the interval below that coatom.

Stating the cover for intervals rather than for the whole lattice is what makes the Solomon--Tits
induction stay inside one lattice: the smaller buildings the induction produces are the intervals
below the coatoms, not proper parts of new lattices.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Simplicial Opposite

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]

/-- The proper part of the interval below `V`. -/
def properBelow (V : L) : Set (properPart L) := {U | U.1 < V}

theorem mem_properBelow {V : L} {U : properPart L} : U ∈ properBelow V ↔ U.1 < V := Iff.rfl

theorem properBelow_top : properBelow (⊤ : L) = Set.univ := by
  ext U
  exact ⟨fun _ => trivial, fun _ => U.2.2⟩

/-- The elements below `V` that do not span it with `p`. -/
def notSpanningBelow (V p : L) : Set (properPart L) := {U | U.1 < V ∧ U.1 ⊔ p ≠ V}

/-- The elements below `V` that do span it with `p`. -/
def spanningBelow (V p : L) : Set (properPart L) := {U | U.1 < V ∧ U.1 ⊔ p = V}

theorem mem_spanningBelow {V p : L} {U : properPart L} :
    U ∈ spanningBelow V p ↔ U.1 < V ∧ U.1 ⊔ p = V := Iff.rfl

theorem notSpanningBelow_subset {V p : L} : notSpanningBelow V p ⊆ properBelow V := fun _ h => h.1

theorem spanningBelow_subset {V p : L} : spanningBelow V p ⊆ properBelow V := fun _ h => h.1

variable [IsModularLattice L]

/-- **An element spanning an interval with an atom is a coatom of that interval.** -/
theorem eq_of_lt_of_spanningBelow {V p : L} (hp : IsAtom p) {U : properPart L}
    (hU : U ∈ spanningBelow V p) {W : L} (hUW : U.1 < W) (hWV : W ≤ V) : W = V := by
  have hle : U.1 ≤ W := le_of_lt hUW
  have hmod : (U.1 ⊔ p) ⊓ W = U.1 ⊔ p ⊓ W := sup_inf_assoc_of_le p hle
  rw [hU.2, inf_eq_right.2 hWV] at hmod
  rcases (hp.le_iff (x := p ⊓ W)).1 inf_le_left with h | h
  · rw [h, sup_bot_eq] at hmod
    exact absurd hmod.symm (ne_of_lt hUW)
  · have hpW : p ≤ W := h ▸ inf_le_right
    have hlew : U.1 ⊔ p ≤ W := sup_le hle hpW
    rw [hU.2] at hlew
    exact le_antisymm hWV hlew

/-- An element of the interval comparable to a spanning coatom lies below it. -/
theorem le_of_mem_generalStar_spanningBelow {V p : L} (hp : IsAtom p) {U : properPart L}
    (hU : U ∈ spanningBelow V p) {X : properPart L} (hX : X ∈ properBelow V)
    (hXU : X ∈ generalStar U) : X.1 ≤ U.1 := by
  rcases hXU with h | h
  · exact h
  · rcases eq_or_lt_of_le (show U.1 ≤ X.1 from h) with h' | h'
    · exact le_of_eq h'.symm
    · exact absurd (eq_of_lt_of_spanningBelow hp hU h' (le_of_lt hX)) (ne_of_lt hX)

/-- **Two pieces meet only inside the base.** -/
theorem starBelow_inter_starBelow {V p : L} (hp : IsAtom p) {U U' : properPart L}
    (hU : U ∈ spanningBelow V p) (hU' : U' ∈ spanningBelow V p) (hne : U ≠ U') :
    properBelow V ∩ (generalStar U ∩ generalStar U') ⊆ notSpanningBelow V p := by
  rintro X ⟨hX, hXU, hXU'⟩
  refine ⟨hX, fun hcon => hne ?_⟩
  have hXsp : X ∈ spanningBelow V p := ⟨hX, hcon⟩
  have h₁ : X.1 = U.1 := by
    refine le_antisymm (le_of_mem_generalStar_spanningBelow hp hU hX hXU) ?_
    rcases eq_or_lt_of_le (le_of_mem_generalStar_spanningBelow hp hU hX hXU) with h | h
    · exact le_of_eq h.symm
    · exact absurd (eq_of_lt_of_spanningBelow hp hXsp h (le_of_lt hU.1)) (ne_of_lt hU.1)
  have h₂ : X.1 = U'.1 := by
    refine le_antisymm (le_of_mem_generalStar_spanningBelow hp hU' hX hXU') ?_
    rcases eq_or_lt_of_le (le_of_mem_generalStar_spanningBelow hp hU' hX hXU') with h | h
    · exact le_of_eq h.symm
    · exact absurd (eq_of_lt_of_spanningBelow hp hXsp h (le_of_lt hU'.1)) (ne_of_lt hU'.1)
  exact Subtype.ext (h₁ ▸ h₂)

/-- **The base meets a piece exactly in the interval below its centre.** -/
theorem notSpanningBelow_inter_star {V p : L} (hp : IsAtom p) {U : properPart L}
    (hU : U ∈ spanningBelow V p) :
    notSpanningBelow V p ∩ generalStar U = properBelow U.1 := by
  ext X
  constructor
  · rintro ⟨hX, hXU⟩
    have hle : X.1 ≤ U.1 := le_of_mem_generalStar_spanningBelow hp hU hX.1 hXU
    rcases eq_or_lt_of_le hle with h | h
    · exact absurd (show X.1 ⊔ p = V by rw [h]; exact hU.2) hX.2
    · exact h
  · intro hlt
    have hXV : X.1 < V := lt_trans hlt hU.1
    refine ⟨⟨hXV, ?_⟩, Or.inl (le_of_lt hlt)⟩
    intro hcon
    have hmod : (X.1 ⊔ p) ⊓ U.1 = X.1 ⊔ p ⊓ U.1 := sup_inf_assoc_of_le p (le_of_lt hlt)
    rw [hcon, inf_eq_right.2 (le_of_lt hU.1)] at hmod
    rcases (hp.le_iff (x := p ⊓ U.1)).1 inf_le_left with h | h
    · rw [h, sup_bot_eq] at hmod
      exact absurd hmod.symm (ne_of_lt hlt)
    · have hpU : p ≤ U.1 := h ▸ inf_le_right
      have : U.1 ⊔ p = U.1 := sup_eq_left.2 hpU
      rw [hU.2] at this
      exact (ne_of_lt hU.1) this.symm

omit [IsModularLattice L] in
/-- **Every chain in the interval lies in the base or in a single piece.** -/
theorem chain_below_mem_base_or_star (V p : L) (n : SimplexCategoryᵒᵖ)
    (x : (nerve (properPart L)).obj n) (hx : ∀ i, x.obj i ∈ properBelow V) :
    (∀ i, x.obj i ∈ notSpanningBelow V p) ∨
      ∃ U : properPart L, U ∈ spanningBelow V p ∧ ∀ i, x.obj i ∈ generalStar U := by
  by_cases hsp : ∃ i, x.obj i ∈ spanningBelow V p
  · obtain ⟨i, hi⟩ := hsp
    refine Or.inr ⟨x.obj i, hi, fun j => ?_⟩
    rcases le_total i j with hij | hij
    · exact Or.inr (leOfHom (x.map (homOfLE hij)))
    · exact Or.inl (leOfHom (x.map (homOfLE hij)))
  · refine Or.inl (fun i => ⟨hx i, fun hcon => hsp ⟨i, ⟨hx i, hcon⟩⟩⟩)

end GaloisForLFunctions.HTGeometry
