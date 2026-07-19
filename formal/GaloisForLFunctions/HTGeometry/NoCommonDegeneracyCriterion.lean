import GaloisForLFunctions.HTGeometry.FiniteSubcoverPacket

/-!
# Patchwise density from absence of a common degeneracy

A single packet cannot in general witness a whole compact patch of shifts: its degeneracy locus in
the shift can meet the patch for an open set of parameters.  A finite family can, provided its
members do not all degenerate at the same shift.

So the patchwise obligation is discharged by exhibiting a finite family of packets with no common
degeneracy — and it suffices that this hold on a dense set of parameters, not everywhere.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **No common degeneracy gives the patchwise condition outright.**  If some finite family of data
never degenerates simultaneously on the patch, every parameter witnesses every shift of it. -/
theorem forall_mem_compact_exists_ne_zero_of_no_common_zero
    {X S Z : Type*} (f : Z → X × S → ℂ) {K : Set S} (F : Finset Z)
    (hnc : ∀ (x : X) (s : S), s ∈ K → ∃ z ∈ F, f z (x, s) ≠ 0) :
    ∀ x : X, ∀ s ∈ K, ∃ z, f z (x, s) ≠ 0 := by
  intro x s hs
  obtain ⟨z, _, hz⟩ := hnc x s hs
  exact ⟨z, hz⟩

/-- **Patchwise density from a dense absence of common degeneracy.**  It is enough that on a dense
set of parameters some finite family of data avoids simultaneous degeneracy throughout the patch. -/
theorem dense_setOf_forall_compact_exists_ne_zero_of_dense_no_common_zero
    {X S Z : Type*} [TopologicalSpace X]
    (f : Z → X × S → ℂ) {K : Set S} {D : Set X} (hD : Dense D) (F : Finset Z)
    (hnc : ∀ x ∈ D, ∀ s ∈ K, ∃ z ∈ F, f z (x, s) ≠ 0) :
    Dense {x : X | ∀ s ∈ K, ∃ z, f z (x, s) ≠ 0} := by
  refine hD.mono ?_
  intro x hx s hs
  obtain ⟨z, _, hz⟩ := hnc x hx s hs
  exact ⟨z, hz⟩

/-- **Global genericity from a per-patch family without common degeneracy.**  Combining with the
compact exhaustion: if every patch admits such a family on a dense set of parameters, the parameters
witnessing every shift are dense and residual. -/
theorem dense_and_residual_of_dense_no_common_zero
    {X S Z : Type*} [TopologicalSpace X] [BaireSpace X] [TopologicalSpace S]
    (f : Z → X × S → ℂ) (hf : ∀ z, Continuous (f z))
    (K : ℕ → Set S) (hcover : ∀ s : S, ∃ m, s ∈ K m) (hK : ∀ m, IsCompact (K m))
    (D : ℕ → Set X) (hD : ∀ m, Dense (D m)) (F : ℕ → Finset Z)
    (hnc : ∀ (m : ℕ), ∀ x ∈ D m, ∀ s ∈ K m, ∃ z ∈ F m, f z (x, s) ≠ 0) :
    Dense {x : X | ∀ s, ∃ z, f z (x, s) ≠ 0} ∧
      {x : X | ∀ s, ∃ z, f z (x, s) ≠ 0} ∈ residual X :=
  dense_and_residual_of_patchwise_exists_ne_zero f K hcover
    (fun m => dense_setOf_forall_compact_exists_ne_zero_of_dense_no_common_zero f
      (hD m) (F m) (hnc m))
    hf hK

end

end GaloisForLFunctions.HTGeometry
