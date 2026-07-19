import GaloisForLFunctions.HTGeometry.SingleShiftFailureThin

/-!
# A compact patch is witnessed by finitely many packets

For a fixed parameter the witness condition is open in the shift, since nonvanishing of a continuous
function is an open condition and the packet existential is a union of such.  A compact patch of
shifts is therefore covered by finitely many of those open sets.

So witnessing every shift of a patch is equivalent to witnessing it with a *finite* set of packets.
The finite set depends on the parameter; no uniform choice is claimed.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Compactness makes the packet existential finite.**  At a fixed parameter, witnessing every
shift of a compact patch is equivalent to witnessing it with finitely many packets. -/
theorem forall_mem_compact_exists_ne_zero_iff_finset
    {X S Z : Type*} [TopologicalSpace S]
    (f : Z → X × S → ℂ) (x : X)
    (hf : ∀ z, Continuous fun s => f z (x, s))
    {K : Set S} (hK : IsCompact K) :
    (∀ s ∈ K, ∃ z, f z (x, s) ≠ 0) ↔
      ∃ F : Finset Z, ∀ s ∈ K, ∃ z ∈ F, f z (x, s) ≠ 0 := by
  classical
  constructor
  · intro h
    have hopen : ∀ z : Z, IsOpen {s : S | f z (x, s) ≠ 0} := fun z =>
      isOpen_compl_singleton.preimage (hf z)
    have hcover : K ⊆ ⋃ z : Z, {s : S | f z (x, s) ≠ 0} := by
      intro s hs
      obtain ⟨z, hz⟩ := h s hs
      exact Set.mem_iUnion.2 ⟨z, hz⟩
    obtain ⟨F, hF⟩ := hK.elim_finite_subcover _ hopen hcover
    refine ⟨F, ?_⟩
    intro s hs
    obtain ⟨z, hz⟩ := Set.mem_iUnion.1 (hF hs)
    obtain ⟨hzF, hzne⟩ := Set.mem_iUnion.1 hz
    exact ⟨z, hzF, hzne⟩
  · rintro ⟨F, hF⟩ s hs
    obtain ⟨z, _, hz⟩ := hF s hs
    exact ⟨z, hz⟩

/-- The patchwise witness condition as a countable union over finite packet sets.  Each member is
the condition that one fixed finite family of packets covers the whole patch. -/
theorem setOf_forall_compact_exists_ne_zero_eq_iUnion_finset
    {X S Z : Type*} [TopologicalSpace S]
    (f : Z → X × S → ℂ)
    (hf : ∀ (x : X) (z : Z), Continuous fun s => f z (x, s))
    {K : Set S} (hK : IsCompact K) :
    {x : X | ∀ s ∈ K, ∃ z, f z (x, s) ≠ 0} =
      ⋃ F : Finset Z, {x : X | ∀ s ∈ K, ∃ z ∈ F, f z (x, s) ≠ 0} := by
  classical
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  exact forall_mem_compact_exists_ne_zero_iff_finset f x (hf x) hK

end

end GaloisForLFunctions.HTGeometry
