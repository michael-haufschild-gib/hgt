import GaloisForLFunctions.HTGeometry.PatchwiseToGlobalGenericity

/-!
# The patchwise density criterion

The one statement still needed for the shift quantifier is density of the patchwise witness
condition.  Since that condition is open, density is equivalent to its failure locus having empty
interior, and the failure locus is explicit: parameters at which some shift of the patch degenerates
against *every* choice of datum simultaneously.

Recording the criterion in that form makes the remaining obligation checkable, and makes clear how
strong the failure is: a single datum with nonvanishing value anywhere in the family suffices to
escape it.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The failure locus of the patchwise witness condition: parameters at which some shift of the
patch kills every datum at once. -/
def patchwiseFailure {X S ζ : Type*} (f : ζ → X × S → ℂ) (K : Set S) : Set X :=
  {x : X | ∃ s ∈ K, ∀ c, f c (x, s) = 0}

/-- The patchwise witness condition is the complement of its failure locus. -/
theorem setOf_forall_compact_exists_ne_zero_eq_compl
    {X S ζ : Type*} (f : ζ → X × S → ℂ) (K : Set S) :
    {x : X | ∀ s ∈ K, ∃ c, f c (x, s) ≠ 0} = (patchwiseFailure f K)ᶜ := by
  ext x
  simp only [patchwiseFailure, Set.mem_setOf_eq, Set.mem_compl_iff, not_exists]
  constructor
  · rintro h s ⟨hs, hall⟩
    obtain ⟨c, hc⟩ := h s hs
    exact hc (hall c)
  · intro h s hs
    by_contra hcon
    push Not at hcon
    exact h s ⟨hs, hcon⟩

/-- **The patchwise density criterion.**  Density of the patchwise witness condition is exactly
emptiness of the interior of its failure locus. -/
theorem dense_setOf_forall_compact_exists_ne_zero_iff
    {X S ζ : Type*} [TopologicalSpace X] (f : ζ → X × S → ℂ) (K : Set S) :
    Dense {x : X | ∀ s ∈ K, ∃ c, f c (x, s) ≠ 0} ↔
      interior (patchwiseFailure f K) = ∅ := by
  rw [setOf_forall_compact_exists_ne_zero_eq_compl]
  exact interior_eq_empty_iff_dense_compl.symm

/-- **Global genericity from an empty-interior failure locus.**  If the shift space is exhausted by
compact patches and each patchwise failure locus has empty interior, the parameters witnessing every
shift are dense and residual. -/
theorem dense_and_residual_of_patchwiseFailure_interior_eq_empty
    {X S ζ : Type*} [TopologicalSpace X] [BaireSpace X] [TopologicalSpace S]
    (f : ζ → X × S → ℂ) (hf : ∀ c, Continuous (f c))
    (K : ℕ → Set S) (hcover : ∀ s : S, ∃ m, s ∈ K m) (hK : ∀ m, IsCompact (K m))
    (hint : ∀ m, interior (patchwiseFailure f (K m)) = ∅) :
    Dense {x : X | ∀ s, ∃ c, f c (x, s) ≠ 0} ∧
      {x : X | ∀ s, ∃ c, f c (x, s) ≠ 0} ∈ residual X :=
  dense_and_residual_of_patchwise_exists_ne_zero f K hcover
    (fun m => (dense_setOf_forall_compact_exists_ne_zero_iff f (K m)).2 (hint m)) hf hK

end

end GaloisForLFunctions.HTGeometry
