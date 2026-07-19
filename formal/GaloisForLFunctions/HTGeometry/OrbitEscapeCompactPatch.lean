import GaloisForLFunctions.HTGeometry.NevanlinnaJetJointContinuity

/-!
# Escaping a degeneracy locus along a group of translations

The compactness step and the escape step are independent, and separating them shows exactly what a
translation family must supply.

Compactness upgrades a *pointwise* escape — every shift of the patch is carried off the degeneracy
locus by some group element — to a *finite* family of group elements serving the whole patch.  That
part is free.

Pointwise escape is not free.  It holds when the action is transitive, since then any single point
off the locus can be carried onto any shift.  For an action with small orbits it is a genuine
condition: the orbit of a shift must meet the complement of the locus.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Compactness upgrades pointwise escape to a finite family.**  If every shift of a compact patch
is carried off a closed locus by some group element, finitely many elements suffice for the whole
patch. -/
theorem exists_finset_escape_of_pointwise
    {S G : Type*} [TopologicalSpace S] (act : G → S → S)
    (hcont : ∀ g, Continuous (act g))
    {D : Set S} (hDclosed : IsClosed D)
    {K : Set S} (hK : IsCompact K)
    (hescape : ∀ s ∈ K, ∃ g : G, act g s ∉ D) :
    ∃ T : Finset G, ∀ s ∈ K, ∃ g ∈ T, act g s ∉ D := by
  classical
  have hopen : ∀ g : G, IsOpen {s : S | act g s ∉ D} := fun g =>
    hDclosed.isOpen_compl.preimage (hcont g)
  have hcover : K ⊆ ⋃ g : G, {s : S | act g s ∉ D} := by
    intro s hs
    obtain ⟨g, hg⟩ := hescape s hs
    exact Set.mem_iUnion.2 ⟨g, hg⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover _ hopen hcover
  refine ⟨T, ?_⟩
  intro s hs
  obtain ⟨g, hg⟩ := Set.mem_iUnion.1 (hT hs)
  obtain ⟨hgT, hgne⟩ := Set.mem_iUnion.1 hg
  exact ⟨g, hgT, hgne⟩

/-- **A transitive action escapes pointwise from a single escape point.**  If some point lies off the
locus and the action can carry it onto any shift, every shift escapes. -/
theorem exists_escape_of_transitive
    {S G : Type*} (act : G → S → S)
    (htrans : ∀ s p : S, ∃ g : G, act g s = p)
    {D : Set S} (hDne : ∃ p : S, p ∉ D) :
    ∀ s : S, ∃ g : G, act g s ∉ D := by
  obtain ⟨p, hp⟩ := hDne
  intro s
  obtain ⟨g, hg⟩ := htrans s p
  exact ⟨g, by rw [hg]; exact hp⟩

/-- **Finite escape from transitivity.**  Combining the two: a transitive action with one point off a
closed locus escapes a whole compact patch with finitely many elements. -/
theorem exists_finset_escape_of_transitive
    {S G : Type*} [TopologicalSpace S] (act : G → S → S)
    (hcont : ∀ g, Continuous (act g))
    (htrans : ∀ s p : S, ∃ g : G, act g s = p)
    {D : Set S} (hDclosed : IsClosed D) (hDne : ∃ p : S, p ∉ D)
    {K : Set S} (hK : IsCompact K) :
    ∃ T : Finset G, ∀ s ∈ K, ∃ g ∈ T, act g s ∉ D :=
  exists_finset_escape_of_pointwise act hcont hDclosed hK
    (fun s _ => exists_escape_of_transitive act htrans hDne s)

end

end GaloisForLFunctions.HTGeometry
