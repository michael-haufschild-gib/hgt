import GaloisForLFunctions.HTGeometry.CountableResidualIntersection

/-!
# Choosing genericity data uniformly over a countable index

Each member of a countable family supplies its own genericity datum — for the expanded rank
condition, a choice of nodes — together with an open dense set of parameters that works for it.

Choice over the countable index turns that family of existentials into a single chosen assignment,
whose associated conditions intersect to a dense residual set.  This is the shape in which
per-pattern genericity statements are combined.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Uniform choice of genericity data.**  If each member of a countable family admits a datum
satisfying a side condition and carrying an open dense set of parameters, then there is a single
assignment of data whose conditions hold simultaneously on a dense residual set. -/
theorem exists_choice_dense_and_residual
    {X ι : Type*} [TopologicalSpace X] [BaireSpace X] [Countable ι]
    {α : ι → Type*} (P : (i : ι) → α i → Prop) (G : (i : ι) → α i → Set X)
    (h : ∀ i, ∃ z : α i, P i z ∧ IsOpen (G i z) ∧ Dense (G i z)) :
    ∃ zc : (i : ι) → α i, (∀ i, P i (zc i)) ∧
      Dense {x : X | ∀ i, x ∈ G i (zc i)} ∧
      {x : X | ∀ i, x ∈ G i (zc i)} ∈ residual X := by
  classical
  choose zc hP hopen hdense using h
  obtain ⟨hd, hr⟩ :=
    dense_and_residual_setOf_forall (fun i => G i (zc i)) hopen hdense
  exact ⟨zc, hP, hd, hr⟩

/-- The same with the family indexed by a pair, so that a countable auxiliary index — a compact
exhaustion, say — can be carried alongside the primary one. -/
theorem exists_choice_dense_and_residual_pair
    {X ι J : Type*} [TopologicalSpace X] [BaireSpace X] [Countable ι] [Countable J]
    {α : ι → J → Type*} (P : (i : ι) → (j : J) → α i j → Prop)
    (G : (i : ι) → (j : J) → α i j → Set X)
    (h : ∀ i j, ∃ z : α i j, P i j z ∧ IsOpen (G i j z) ∧ Dense (G i j z)) :
    ∃ zc : (i : ι) → (j : J) → α i j, (∀ i j, P i j (zc i j)) ∧
      Dense {x : X | ∀ i j, x ∈ G i j (zc i j)} ∧
      {x : X | ∀ i j, x ∈ G i j (zc i j)} ∈ residual X := by
  classical
  obtain ⟨zp, hP, hd, hr⟩ :=
    exists_choice_dense_and_residual
      (ι := ι × J) (α := fun q => α q.1 q.2)
      (fun q z => P q.1 q.2 z) (fun q z => G q.1 q.2 z)
      (fun q => h q.1 q.2)
  refine ⟨fun i j => zp (i, j), fun i j => hP (i, j), ?_, ?_⟩
  · have hset : {x : X | ∀ q : ι × J, x ∈ G q.1 q.2 (zp q)} =
        {x : X | ∀ i j, x ∈ G i j (zp (i, j))} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hx i j
        exact hx (i, j)
      · rintro hx ⟨i, j⟩
        exact hx i j
    rwa [hset] at hd
  · have hset : {x : X | ∀ q : ι × J, x ∈ G q.1 q.2 (zp q)} =
        {x : X | ∀ i j, x ∈ G i j (zp (i, j))} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hx i j
        exact hx (i, j)
      · rintro hx ⟨i, j⟩
        exact hx i j
    rwa [hset] at hr

end

end GaloisForLFunctions.HTGeometry
