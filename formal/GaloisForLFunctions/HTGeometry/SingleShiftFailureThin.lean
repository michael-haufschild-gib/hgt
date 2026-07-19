import GaloisForLFunctions.HTGeometry.CountablePacketReduction

/-!
# The failure set at a single shift is nowhere dense

At one fixed shift, the parameters degenerating against every packet are contained in those
degenerating against one particular packet, and the genericity theorem supplies a packet whose
nondegeneracy set is dense.  So the single-shift failure set has empty interior.

The patchwise failure locus is the union of these over a compact patch of shifts.  That union is
closed, but its emptiness of interior does not follow from the pieces being thin, since the union is
uncountable; this file records exactly the part that does follow.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **A single-shift failure set is nowhere dense.**  If some datum has a dense nonvanishing set,
the parameters annihilating every datum have empty interior. -/
theorem interior_setOf_forall_eq_zero_eq_empty
    {X Z : Type*} [TopologicalSpace X] (g : Z → X → ℂ) (z₀ : Z)
    (hdense : Dense {x : X | g z₀ x ≠ 0}) :
    interior {x : X | ∀ z, g z x = 0} = ∅ := by
  have hsub : {x : X | ∀ z, g z x = 0} ⊆ {x : X | g z₀ x ≠ 0}ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
    exact hx z₀
  have hempty : interior ({x : X | g z₀ x ≠ 0}ᶜ) = ∅ :=
    interior_eq_empty_iff_dense_compl.2 (by simpa using hdense)
  exact Set.eq_empty_of_subset_empty (hempty ▸ interior_mono hsub)

/-- The same restricted to a dense family of data, the form left by the countable packet
reduction. -/
theorem interior_setOf_forall_mem_eq_zero_eq_empty
    {X Z : Type*} [TopologicalSpace X] (g : Z → X → ℂ) {Q : Set Z} {z₀ : Z} (hz₀ : z₀ ∈ Q)
    (hdense : Dense {x : X | g z₀ x ≠ 0}) :
    interior {x : X | ∀ z ∈ Q, g z x = 0} = ∅ := by
  have hsub : {x : X | ∀ z ∈ Q, g z x = 0} ⊆ {x : X | g z₀ x ≠ 0}ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
    exact hx z₀ hz₀
  have hempty : interior ({x : X | g z₀ x ≠ 0}ᶜ) = ∅ :=
    interior_eq_empty_iff_dense_compl.2 (by simpa using hdense)
  exact Set.eq_empty_of_subset_empty (hempty ▸ interior_mono hsub)

/-- **A single shift never blocks genericity.**  For a fixed shift admitting a datum with dense
nonvanishing set, the parameters witnessing that shift are dense. -/
theorem dense_setOf_exists_ne_zero_of_dense
    {X Z : Type*} [TopologicalSpace X] (g : Z → X → ℂ) (z₀ : Z)
    (hdense : Dense {x : X | g z₀ x ≠ 0}) :
    Dense {x : X | ∃ z, g z x ≠ 0} :=
  hdense.mono fun _ hx => ⟨z₀, hx⟩

end

end GaloisForLFunctions.HTGeometry
