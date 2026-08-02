import GaloisForLFunctions.HTGeometry.NerveSubcomplex
import GaloisForLFunctions.HTGeometry.NerveVertexRemoval

/-!
# The cover of a building by the non-spanning elements and the stars of the coatoms

Fix an atom `p` of a bounded modular lattice.  Every proper nonzero element either fails to span
with `p`, or spans with it, and the elements that span with an atom are exactly coatoms.  This gives
a cover of the order complex of the proper part:

* the base is the full subcomplex spanned by the elements that do not span with `p`;
* there is one further piece for each element that does span, namely its star.

The cover has the two properties a Mayer--Vietoris argument over an arbitrary index needs.  Two
distinct pieces meet only inside the base, because an element comparable to two distinct coatoms
cannot itself be a coatom.  And the base meets a piece exactly in the elements strictly below that
coatom — the proper part of the interval below it, which is a building one step smaller.

Every chain lies in the base or in a single piece: if some member spans, all the others are
comparable to it, since they lie in a chain.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Simplicial Opposite

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]

/-- The proper nonzero elements of a bounded lattice. -/
abbrev properPart (L : Type u) [Lattice L] [BoundedOrder L] : Type u :=
  {U : L // ⊥ < U ∧ U < ⊤}

/-- The proper nonzero elements that do not span with `p`. -/
def notSpanning (p : L) : Set (properPart L) := {U | (U : L) ⊔ p ≠ ⊤}

/-- The proper nonzero elements that span with `p`. -/
def spanning (p : L) : Set (properPart L) := {U | (U : L) ⊔ p = ⊤}

theorem mem_spanning_iff {p : L} {U : properPart L} : U ∈ spanning p ↔ (U : L) ⊔ p = ⊤ := Iff.rfl

theorem notMem_notSpanning_iff {p : L} {U : properPart L} :
    U ∉ notSpanning p ↔ U ∈ spanning p := by
  simp [notSpanning, spanning]

/-- **A coatom below a coatom is equal to it.** -/
theorem eq_of_isCoatom_le {U V : L} (hU : IsCoatom U) (hV : IsCoatom V) (h : U ≤ V) : U = V := by
  rcases eq_or_lt_of_le h with h | h
  · exact h
  · exact absurd (hU.2 V h) hV.1

variable [IsModularLattice L]

/-- **An element that spans with an atom is a coatom.**  If something sits strictly above it, then
by modularity the atom either misses it — forcing equality — or lies below it, forcing the top. -/
theorem isCoatom_of_spanning {p : L} (hp : IsAtom p) {V : properPart L} (hV : V ∈ spanning p) :
    IsCoatom (V : L) := by
  refine ⟨ne_of_lt V.2.2, fun W hW => ?_⟩
  have hle : (V : L) ≤ W := le_of_lt hW
  have hmod : ((V : L) ⊔ p) ⊓ W = (V : L) ⊔ p ⊓ W := sup_inf_assoc_of_le p hle
  rw [mem_spanning_iff.1 hV, top_inf_eq] at hmod
  rcases (hp.le_iff (x := p ⊓ W)).1 inf_le_left with h | h
  · rw [h, sup_bot_eq] at hmod
    exact absurd hmod.symm (ne_of_lt hW)
  · have hpW : p ≤ W := h ▸ inf_le_right
    have hlew : (V : L) ⊔ p ≤ W := sup_le hle hpW
    rw [mem_spanning_iff.1 hV] at hlew
    exact top_le_iff.1 hlew

/-- An element comparable to a spanning coatom is either below it or equal to it. -/
theorem le_of_mem_generalStar_spanning {p : L} (hp : IsAtom p) {V : properPart L}
    (hV : V ∈ spanning p) {U : properPart L} (hU : U ∈ generalStar V) : (U : L) ≤ (V : L) := by
  have hVco : IsCoatom (V : L) := isCoatom_of_spanning hp hV
  rcases hU with h | h
  · exact h
  · rcases eq_or_lt_of_le (show (V : L) ≤ (U : L) from h) with h' | h'
    · exact le_of_eq h'.symm
    · exact absurd (hVco.2 (U : L) h') (ne_of_lt U.2.2)

/-- **Two distinct pieces meet only inside the base.**  An element comparable to two distinct
spanning elements cannot span. -/
theorem star_inter_star_subset_notSpanning {p : L} (hp : IsAtom p) {V V' : properPart L}
    (hV : V ∈ spanning p) (hV' : V' ∈ spanning p) (hne : V ≠ V') :
    generalStar V ∩ generalStar V' ⊆ notSpanning p := by
  rintro U ⟨hUV, hUV'⟩
  by_contra hU
  have hUsp : U ∈ spanning p := notMem_notSpanning_iff.1 hU
  have hUco : IsCoatom (U : L) := isCoatom_of_spanning hp hUsp
  have h₁ : (U : L) = (V : L) :=
    eq_of_isCoatom_le hUco (isCoatom_of_spanning hp hV)
      (le_of_mem_generalStar_spanning hp hV hUV)
  have h₂ : (U : L) = (V' : L) :=
    eq_of_isCoatom_le hUco (isCoatom_of_spanning hp hV')
      (le_of_mem_generalStar_spanning hp hV' hUV')
  exact hne (Subtype.ext (h₁ ▸ h₂))

/-- **The base meets a piece exactly in the elements strictly below it.**  Something comparable to a
spanning coatom either lies strictly below it or is it, and it spans; conversely something strictly
below a coatom complementary to `p` cannot span, by modularity. -/
theorem notSpanning_inter_star {p : L} (hp : IsAtom p) {V : properPart L} (hV : V ∈ spanning p) :
    notSpanning p ∩ generalStar V = {U : properPart L | U < V} := by
  ext U
  constructor
  · rintro ⟨hU, hUV⟩
    have hle : (U : L) ≤ (V : L) := le_of_mem_generalStar_spanning hp hV hUV
    rcases eq_or_lt_of_le hle with h | h
    · exact absurd (mem_spanning_iff.2 (h ▸ mem_spanning_iff.1 hV)) hU
    · exact h
  · intro hlt
    refine ⟨?_, Or.inl (le_of_lt hlt)⟩
    intro hUsp
    have hle : (U : L) ≤ (V : L) := le_of_lt hlt
    have hmod : ((U : L) ⊔ p) ⊓ (V : L) = (U : L) ⊔ p ⊓ (V : L) := sup_inf_assoc_of_le p hle
    rw [(show (U : L) ⊔ p = ⊤ from hUsp), top_inf_eq] at hmod
    rcases (hp.le_iff (x := p ⊓ (V : L))).1 inf_le_left with h | h
    · rw [h, sup_bot_eq] at hmod
      exact absurd hmod.symm (ne_of_lt hlt)
    · have hpV : p ≤ (V : L) := h ▸ inf_le_right
      have hsup : (V : L) ⊔ p = (V : L) := sup_eq_left.2 hpV
      rw [mem_spanning_iff.1 hV] at hsup
      exact (ne_of_lt V.2.2) hsup.symm

omit [IsModularLattice L] in
/-- **Every chain lies in the base or in a single piece.**  If one of its members spans, the others
are comparable to it. -/
theorem chain_mem_base_or_star (p : L) (n : SimplexCategoryᵒᵖ)
    (x : (nerve (properPart L)).obj n) :
    (∀ i, x.obj i ∈ notSpanning p) ∨
      ∃ V : properPart L, V ∈ spanning p ∧ ∀ i, x.obj i ∈ generalStar V := by
  by_cases hx : ∃ i, x.obj i ∈ spanning p
  · obtain ⟨i, hi⟩ := hx
    refine Or.inr ⟨x.obj i, hi, fun j => ?_⟩
    rcases le_total i j with hij | hij
    · exact Or.inr (leOfHom (x.map (homOfLE hij)))
    · exact Or.inl (leOfHom (x.map (homOfLE hij)))
  · exact Or.inl (fun i hi => hx ⟨i, hi⟩)

/-- **A base and a family span a covering exactly when every simplex lies entirely in one of
them.** -/
theorem nerveSubcomplex_sup_iSup_eq_top {P : Type u} [PartialOrder P] {Q₀ : Set P} {ι : Type u}
    {Q : ι → Set P}
    (h : ∀ (n : SimplexCategoryᵒᵖ) (x : (nerve P).obj n),
      (∀ i, x.obj i ∈ Q₀) ∨ ∃ a, ∀ i, x.obj i ∈ Q a) :
    nerveSubcomplex Q₀ ⊔ ⨆ a, nerveSubcomplex (Q a) = ⊤ := by
  refine Subfunctor.ext (funext fun U => ?_)
  ext x
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  rcases h U x with h₀ | ⟨a, ha⟩
  · exact Or.inl h₀
  · exact Or.inr ((le_iSup (fun a => nerveSubcomplex (Q a)) a) U ha)

omit [IsModularLattice L] in
/-- **The cover of a building.**  The elements that do not span with a fixed atom, together with the
stars of the elements that do span, cover the order complex of the proper part. -/
theorem nerveSubcomplex_notSpanning_sup_iSup_star (p : L) :
    nerveSubcomplex (notSpanning p)
        ⊔ ⨆ V : {V : properPart L // V ∈ spanning p}, nerveSubcomplex (generalStar (V : properPart L))
      = ⊤ :=
  nerveSubcomplex_sup_iSup_eq_top (fun n x => by
    rcases chain_mem_base_or_star p n x with h | ⟨V, hV, hstar⟩
    · exact Or.inl h
    · exact Or.inr ⟨⟨V, hV⟩, hstar⟩)

end GaloisForLFunctions.HTGeometry
