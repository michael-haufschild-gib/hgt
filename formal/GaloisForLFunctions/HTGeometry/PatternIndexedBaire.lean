import GaloisForLFunctions.HTGeometry.CountableDifferentialPattern
import Mathlib.Topology.Baire.Lemmas

/-!
# Intersecting genericity over all differential patterns

The freeness predicate quantifies over every finite differential pattern.  That quantifier is
countable: a pattern is finite combinatorial data over a countable shift palette, and the corpus
records `Countable (FiniteDifferentialPattern Γ)`.

So a genericity statement proved open and dense for each individual pattern intersects to a dense
statement over all of them at once.  This is the last quantifier of the freeness predicate that has
to be discharged by a Baire argument; the shift and packet quantifiers are handled separately by the
compact-patch reduction.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- **Genericity over all patterns.**  A property that is open and dense for each finite
differential pattern holds, densely, for all patterns simultaneously. -/
theorem dense_setOf_forall_pattern
    {X : Type*} [TopologicalSpace X] [BaireSpace X]
    (G : FiniteDifferentialPattern Unit → Set X)
    (hopen : ∀ p, IsOpen (G p)) (hdense : ∀ p, Dense (G p)) :
    Dense {x : X | ∀ p, x ∈ G p} := by
  have hinter := dense_iInter_of_isOpen hopen hdense
  have hset : (⋂ p, G p) = {x : X | ∀ p, x ∈ G p} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
  rwa [hset] at hinter

/-- The same statement for a property indexed by patterns paired with a countable auxiliary index,
which is the form produced by combining the pattern quantifier with a compact exhaustion. -/
theorem dense_setOf_forall_pattern_and_index
    {X ι : Type*} [TopologicalSpace X] [BaireSpace X] [Countable ι]
    (G : FiniteDifferentialPattern Unit → ι → Set X)
    (hopen : ∀ p i, IsOpen (G p i)) (hdense : ∀ p i, Dense (G p i)) :
    Dense {x : X | ∀ p i, x ∈ G p i} := by
  have hopen' : ∀ q : FiniteDifferentialPattern Unit × ι, IsOpen (G q.1 q.2) :=
    fun q => hopen q.1 q.2
  have hdense' : ∀ q : FiniteDifferentialPattern Unit × ι, Dense (G q.1 q.2) :=
    fun q => hdense q.1 q.2
  have hinter := dense_iInter_of_isOpen hopen' hdense'
  have hset : (⋂ q : FiniteDifferentialPattern Unit × ι, G q.1 q.2) =
      {x : X | ∀ p i, x ∈ G p i} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h p i
      exact h (p, i)
    · rintro h ⟨p, i⟩
      exact h p i
  rwa [hset] at hinter

end

end GaloisForLFunctions.HTGeometry
