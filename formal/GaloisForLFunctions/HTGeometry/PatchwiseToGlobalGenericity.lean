import GaloisForLFunctions.HTGeometry.CompactShiftPatchOpenness

/-!
# From patchwise genericity to a global shift quantifier

An uncountable quantifier over shifts becomes tractable once the shift space is exhausted by
countably many patches: a condition holding open and densely on each patch holds densely, and
residually, for every shift at once.

This isolates what an uncountable shift quantifier actually costs.  The global statement follows
formally from the patchwise ones; the only mathematical content left is the density of a single
patchwise condition.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Patchwise genericity gives global genericity.**  If the shift space is covered by countably
many patches, and for each patch the parameters satisfying the condition throughout that patch form
an open dense set, then the parameters satisfying it at every shift are dense and residual. -/
theorem dense_and_residual_of_patchwise
    {X S : Type*} [TopologicalSpace X] [BaireSpace X]
    (K : ℕ → Set S) (hcover : ∀ s : S, ∃ m, s ∈ K m)
    (G : ℕ → Set X) (hopen : ∀ m, IsOpen (G m)) (hdense : ∀ m, Dense (G m))
    (P : X → S → Prop)
    (hGP : ∀ (m : ℕ) (x : X), x ∈ G m → ∀ s ∈ K m, P x s) :
    Dense {x : X | ∀ s, P x s} ∧ {x : X | ∀ s, P x s} ∈ residual X := by
  classical
  obtain ⟨hd, hr⟩ := dense_and_residual_setOf_forall G hopen hdense
  have hsub : {x : X | ∀ m, x ∈ G m} ⊆ {x : X | ∀ s, P x s} := by
    intro x hx s
    obtain ⟨m, hm⟩ := hcover s
    exact hGP m x (hx m) s hm
  exact ⟨hd.mono hsub, Filter.mem_of_superset hr hsub⟩

/-- The same with the patchwise condition stated as the one produced by the compact-patch openness
lemma: at every shift of the patch some datum has nonvanishing value. -/
theorem dense_and_residual_of_patchwise_exists_ne_zero
    {X S ζ : Type*} [TopologicalSpace X] [BaireSpace X] [TopologicalSpace S]
    (f : ζ → X × S → ℂ)
    (K : ℕ → Set S) (hcover : ∀ s : S, ∃ m, s ∈ K m)
    (hdense : ∀ m, Dense {x : X | ∀ s ∈ K m, ∃ c, f c (x, s) ≠ 0})
    (hf : ∀ c, Continuous (f c)) (hK : ∀ m, IsCompact (K m)) :
    Dense {x : X | ∀ s, ∃ c, f c (x, s) ≠ 0} ∧
      {x : X | ∀ s, ∃ c, f c (x, s) ≠ 0} ∈ residual X := by
  refine dense_and_residual_of_patchwise K hcover
    (fun m => {x : X | ∀ s ∈ K m, ∃ c, f c (x, s) ≠ 0})
    (fun m => isOpen_setOf_forall_compact_exists_ne_zero f hf (hK m)) hdense
    (fun x s => ∃ c, f c (x, s) ≠ 0) ?_
  intro m x hx s hs
  exact hx s hs

end

end GaloisForLFunctions.HTGeometry
