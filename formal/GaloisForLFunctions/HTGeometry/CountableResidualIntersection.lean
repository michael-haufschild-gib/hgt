import GaloisForLFunctions.HTGeometry.PatternIndexedBaire

/-!
# Countable intersections of open dense conditions

A genericity conclusion that holds open and densely for each member of a countable family holds
densely, and residually, for all members at once.  Density is the Baire property; residuality is the
countable-intersection property of the residual filter.

The pattern quantifier of the freeness predicate is countable, so this is the form in which the
per-pattern genericity statements are combined.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Countable intersection of open dense conditions is dense and residual.** -/
theorem dense_and_residual_setOf_forall
    {X : Type*} [TopologicalSpace X] [BaireSpace X] {ι : Type*} [Countable ι]
    (G : ι → Set X) (hopen : ∀ i, IsOpen (G i)) (hdense : ∀ i, Dense (G i)) :
    Dense {x : X | ∀ i, x ∈ G i} ∧ {x : X | ∀ i, x ∈ G i} ∈ residual X := by
  have hset : (⋂ i, G i) = {x : X | ∀ i, x ∈ G i} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [← hset]
    exact dense_iInter_of_isOpen hopen hdense
  · rw [← hset]
    refine countable_iInter_mem.2 ?_
    intro i
    exact residual_of_dense_open (hopen i) (hdense i)

/-- The same for a property indexed by a countable pattern family together with a countable
auxiliary index, the form produced by combining the pattern quantifier with a compact exhaustion. -/
theorem dense_and_residual_setOf_forall_pattern_and_index
    {X ι : Type*} [TopologicalSpace X] [BaireSpace X] [Countable ι]
    (G : FiniteDifferentialPattern Unit → ι → Set X)
    (hopen : ∀ p i, IsOpen (G p i)) (hdense : ∀ p i, Dense (G p i)) :
    Dense {x : X | ∀ p i, x ∈ G p i} ∧
      {x : X | ∀ p i, x ∈ G p i} ∈ residual X := by
  have hpair := dense_and_residual_setOf_forall
    (fun q : FiniteDifferentialPattern Unit × ι => G q.1 q.2)
    (fun q => hopen q.1 q.2) (fun q => hdense q.1 q.2)
  have hset : {x : X | ∀ q : FiniteDifferentialPattern Unit × ι, x ∈ G q.1 q.2} =
      {x : X | ∀ p i, x ∈ G p i} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h p i
      exact h (p, i)
    · rintro h ⟨p, i⟩
      exact h p i
  rw [hset] at hpair
  exact hpair

end

end GaloisForLFunctions.HTGeometry
