import Mathlib

/-!
# Lebesgue covering dimension

The *order* of a family of sets is the largest number of its members that share a point, and the
covering dimension of a space is the least `n` such that every finite open cover admits a finite
open refinement of order at most `n + 1`.

For a compact Hausdorff space this is the classical Lebesgue dimension; the restriction to finite
covers is harmless there because every open cover has a finite subcover.

The two structural facts proved here are that the order condition is monotone and that covering
dimension passes to closed subspaces — the second by enlarging a cover of the subspace with the
complement of its (closed) image.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A family of sets has *order at most* `n` when no point of the space lies in more than `n`
members of the family. -/
def HasOrderLE {ι : Type*} (V : ι → Set X) (n : ℕ) : Prop :=
  ∀ (x : X) (s : Finset ι), (∀ i ∈ s, x ∈ V i) → s.card ≤ n

/-- `HasCoveringDimLE X n` says that every finite open cover of `X` admits a finite open
refinement in which no point lies in more than `n + 1` members. -/
def HasCoveringDimLE (X : Type*) [TopologicalSpace X] (n : ℕ) : Prop :=
  ∀ (m : ℕ) (U : Fin m → Set X), (∀ i, IsOpen (U i)) → (∀ x : X, ∃ i, x ∈ U i) →
    ∃ (p : ℕ) (V : Fin p → Set X), (∀ k, IsOpen (V k)) ∧ (∀ x : X, ∃ k, x ∈ V k) ∧
      (∀ k, ∃ i, V k ⊆ U i) ∧ HasOrderLE V (n + 1)

omit [TopologicalSpace X] in
theorem HasOrderLE.mono {ι : Type*} {V : ι → Set X} {n n' : ℕ} (h : HasOrderLE V n)
    (hn : n ≤ n') : HasOrderLE V n' := fun x s hs => le_trans (h x s hs) hn

theorem HasCoveringDimLE.mono {n n' : ℕ} (h : HasCoveringDimLE X n) (hn : n ≤ n') :
    HasCoveringDimLE X n' := by
  intro m U hUo hUc
  obtain ⟨p, V, hVo, hVc, hVr, hVord⟩ := h m U hUo hUc
  exact ⟨p, V, hVo, hVc, hVr, hVord.mono (by omega)⟩

omit [TopologicalSpace X] in
/-- A family indexed by the empty type has order zero. -/
theorem hasOrderLE_of_isEmpty {ι : Type*} [IsEmpty ι] (V : ι → Set X) (n : ℕ) :
    HasOrderLE V n := by
  intro x s _
  have : s = ∅ := Finset.eq_empty_of_forall_notMem fun i _ => IsEmpty.elim ‹IsEmpty ι› i
  simp [this]

/-- **Covering dimension passes to closed subspaces.**  A cover of the subspace is extended by the
complement of its image, which is open because the image is closed; a refinement of the extended
cover restricts to a refinement of the original one, and restriction cannot raise the order. -/
theorem HasCoveringDimLE.of_isClosedEmbedding {f : Y → X} (hf : IsClosedEmbedding f) {n : ℕ}
    (h : HasCoveringDimLE X n) : HasCoveringDimLE Y n := by
  intro m U hUo hUc
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨0, fun k => k.elim0, fun k => k.elim0, ?_, fun k => k.elim0, ?_⟩
    · intro y
      obtain ⟨i, -⟩ := hUc y
      exact i.elim0
    · exact hasOrderLE_of_isEmpty _ _
  · choose W hWo hWpre using fun i => (hf.isInducing.isOpen_iff).mp (hUo i)
    set W' : Fin (m + 1) → Set X := Fin.snoc W (Set.range f)ᶜ with hW'
    have hW'o : ∀ i, IsOpen (W' i) := by
      intro i
      refine Fin.lastCases ?_ ?_ i
      · simpa [hW'] using hf.isClosed_range.isOpen_compl
      · intro j
        simpa [hW'] using hWo j
    have hW'c : ∀ x : X, ∃ i, x ∈ W' i := by
      intro x
      by_cases hx : x ∈ Set.range f
      · obtain ⟨y, rfl⟩ := hx
        obtain ⟨i, hi⟩ := hUc y
        refine ⟨i.castSucc, ?_⟩
        have : y ∈ f ⁻¹' W i := by rw [hWpre i]; exact hi
        simpa [hW'] using this
      · exact ⟨Fin.last m, by simpa [hW'] using hx⟩
    obtain ⟨p, V, hVo, hVc, hVr, hVord⟩ := h (m + 1) W' hW'o hW'c
    refine ⟨p, fun k => f ⁻¹' (V k), fun k => (hVo k).preimage hf.continuous, ?_, ?_, ?_⟩
    · intro y
      obtain ⟨k, hk⟩ := hVc (f y)
      exact ⟨k, hk⟩
    · intro k
      obtain ⟨i, hi⟩ := hVr k
      refine Fin.lastCases ?_ ?_ i hi
      · intro hi
        refine ⟨⟨0, hm⟩, ?_⟩
        intro y hy
        have hmem := hi hy
        simp only [hW', Fin.snoc_last, Set.mem_compl_iff] at hmem
        exact absurd (Set.mem_range_self y) hmem
      · intro j hi
        refine ⟨j, ?_⟩
        intro y hy
        have : f y ∈ W j := by
          have := hi hy
          simpa [hW'] using this
        have : y ∈ f ⁻¹' W j := this
        rwa [hWpre j] at this
    · intro y s hs
      exact hVord (f y) s hs

/-- Covering dimension is a topological invariant. -/
theorem HasCoveringDimLE.of_homeomorph (e : Y ≃ₜ X) {n : ℕ} (h : HasCoveringDimLE X n) :
    HasCoveringDimLE Y n :=
  h.of_isClosedEmbedding e.isClosedEmbedding

end GaloisForLFunctions.HTGeometry
