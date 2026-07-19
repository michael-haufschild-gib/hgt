import GaloisForLFunctions.HTGeometry.AnalyticLineEscape

/-!
# A residual set of densities with densely many good shifts

The packet theorem gives, for each fixed shift, a residual set of densities witnessing it.  Residual
sets are stable under countable intersection, so intersecting over a countable dense family of
shifts gives a single residual set of densities witnessing all of them.

For such a density the good-shift set is open and contains a dense family, hence is dense; its
complement is closed and nowhere dense.  This falls short of the witness predicate, which demands
*every* shift, and the shortfall is exactly a nowhere dense closed set.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Intersecting residual sets over a countable family stays residual. -/
theorem residual_iInter_of_countable
    {X ι : Type*} [TopologicalSpace X] [Countable ι]
    (R : ι → Set X) (hR : ∀ i, R i ∈ residual X) :
    (⋂ i, R i) ∈ residual X :=
  countable_iInter_mem.2 hR

/-- **An open set containing a dense family is dense.** -/
theorem dense_of_isOpen_of_dense_subset
    {S : Type*} [TopologicalSpace S] {G Q : Set S}
    (hQ : Dense Q) (hsub : Q ⊆ G) : Dense G :=
  hQ.mono hsub

/-- **Densely many good shifts on a residual set of densities.**  If the good-shift set is open for
every density, and a countable dense family of shifts is witnessed on a residual set of densities,
then on that set the good-shift set is dense — so the shifts that fail form a closed nowhere dense
set. -/
theorem dense_goodShift_of_countable_dense_witnessed
    {X S : Type*} [TopologicalSpace X] [TopologicalSpace S]
    (G : X → Set S) (hopen : ∀ x, IsOpen (G x))
    {Q : Set S} (hQ : Dense Q)
    {R : Set X} (hR : ∀ x ∈ R, Q ⊆ G x) :
    ∀ x ∈ R, Dense (G x) ∧ IsClosed (G x)ᶜ ∧ interior ((G x)ᶜ) = ∅ := by
  intro x hx
  have hdense : Dense (G x) := dense_of_isOpen_of_dense_subset hQ (hR x hx)
  refine ⟨hdense, (hopen x).isClosed_compl, ?_⟩
  exact interior_eq_empty_iff_dense_compl.2 (by simpa using hdense)

/-- The witness predicate needs the good-shift set to be everything, which for an open dense set is
the further statement that its complement is empty. -/
theorem forall_mem_goodShift_iff_compl_eq_empty
    {S : Type*} [TopologicalSpace S] (G : Set S) :
    (∀ s : S, s ∈ G) ↔ Gᶜ = ∅ := by
  constructor
  · intro h
    ext s
    simp only [Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
    exact h s
  · intro h s
    by_contra hs
    have : s ∈ Gᶜ := hs
    rw [h] at this
    exact this

end

end GaloisForLFunctions.HTGeometry
