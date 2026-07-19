import GaloisForLFunctions.HTGeometry.NoCommonDegeneracyCriterion

/-!
# Finitely many translates escape a thin degeneracy locus on a compact patch

A single degeneracy locus can meet a compact patch of shifts, so one packet cannot witness the whole
patch.  But if the locus is closed with empty interior, then every shift escapes *some* translate of
it: the translations that fail at a given shift form a closed set with empty interior, so a good
translation exists pointwise.

Escaping a fixed translate is an open condition on the shift, so compactness upgrades the pointwise
statement to a finite family.  Finitely many translates therefore have no common degeneracy on the
patch.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Finitely many translates escape a closed set on a compact patch.**  A single point outside `D`
suffices: every point of a compact set escapes one of finitely many translates of `D`.

No thinness of `D` is required.  Translating the escape point onto a given shift already escapes
there, and escaping a fixed translate is open, so compactness does the rest. -/
theorem exists_finset_translates_notMem
    {S : Type*} [TopologicalSpace S] [AddCommGroup S] [IsTopologicalAddGroup S]
    {D : Set S} (hDclosed : IsClosed D) (hDne : ∃ p : S, p ∉ D)
    {K : Set S} (hK : IsCompact K) :
    ∃ T : Finset S, ∀ s ∈ K, ∃ t ∈ T, s - t ∉ D := by
  classical
  obtain ⟨p, hp⟩ := hDne
  -- Escaping a fixed translate is open in the shift.
  have hopen : ∀ t : S, IsOpen {s : S | s - t ∉ D} := by
    intro t
    have : {s : S | s - t ∉ D} = (fun s : S => s - t) ⁻¹' Dᶜ := rfl
    rw [this]
    exact hDclosed.isOpen_compl.preimage (continuous_id.sub continuous_const)
  -- Every shift escapes some translate: translate the chosen escape point onto it.
  have hcover : K ⊆ ⋃ t : S, {s : S | s - t ∉ D} := by
    intro s _
    refine Set.mem_iUnion.2 ⟨s - p, ?_⟩
    have hsp : s - (s - p) = p := by abel
    simpa [Set.mem_setOf_eq, hsp] using hp
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover _ hopen hcover
  refine ⟨T, ?_⟩
  intro s hs
  obtain ⟨t, ht⟩ := Set.mem_iUnion.1 (hT hs)
  obtain ⟨htT, htne⟩ := Set.mem_iUnion.1 ht
  exact ⟨t, htT, htne⟩

/-- **No common degeneracy for a translate family.**  With the degeneracy locus of a datum closed
and thin, and the value covariant under simultaneous translation of datum and shift, finitely many
translates of that datum never degenerate simultaneously on a compact patch. -/
theorem exists_finset_no_common_zero_of_translation_covariant
    {X S Z : Type*} [TopologicalSpace S] [AddCommGroup S] [IsTopologicalAddGroup S]
    (f : Z → X × S → ℂ) (x : X) (z : Z) (tr : Z → S → Z)
    (hcov : ∀ (t : S) (s : S), f (tr z t) (x, s) = f z (x, s - t))
    (hDclosed : IsClosed {s : S | f z (x, s) = 0})
    (hDne : ∃ s₀ : S, f z (x, s₀) ≠ 0)
    {K : Set S} (hK : IsCompact K) :
    ∃ T : Finset S, ∀ s ∈ K, ∃ t ∈ T, f (tr z t) (x, s) ≠ 0 := by
  obtain ⟨T, hT⟩ := exists_finset_translates_notMem hDclosed hDne hK
  refine ⟨T, ?_⟩
  intro s hs
  obtain ⟨t, htT, htne⟩ := hT s hs
  exact ⟨t, htT, by rw [hcov t s]; exact htne⟩

end

end GaloisForLFunctions.HTGeometry
