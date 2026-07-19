import GaloisForLFunctions.HTGeometry.PatchwiseDensityCriterion

/-!
# Reducing the packet existential to a countable family

The witness condition asks for *some* packet at each shift, and the packet space is uncountable.
But the value depends continuously on the packet, so nonvanishing somewhere is nonvanishing on a
neighbourhood, which meets any dense set of packets.

The existential may therefore be taken over a countable dense family without changing the condition.
This is what makes the failure locus a countable intersection of closed conditions rather than an
arbitrary one.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **A continuous nonvanishing witness can be taken in any dense set.** -/
theorem exists_ne_zero_iff_exists_mem_dense
    {Z : Type*} [TopologicalSpace Z] {Q : Set Z} (hQ : Dense Q)
    (g : Z → ℂ) (hg : Continuous g) :
    (∃ z, g z ≠ 0) ↔ ∃ z ∈ Q, g z ≠ 0 := by
  constructor
  · rintro ⟨z, hz⟩
    have hopen : IsOpen {w : Z | g w ≠ 0} :=
      isOpen_compl_singleton.preimage hg
    obtain ⟨w, hwQ, hwne⟩ := hQ.exists_mem_open hopen ⟨z, hz⟩
    exact ⟨w, hwQ, hwne⟩
  · rintro ⟨z, _, hz⟩
    exact ⟨z, hz⟩

/-- **The witness condition over a countable dense packet family.**  Restricting the packet
existential to a dense set leaves the patchwise condition unchanged. -/
theorem setOf_forall_compact_exists_ne_zero_eq_dense_family
    {X S Z : Type*} [TopologicalSpace Z] {Q : Set Z} (hQ : Dense Q)
    (f : Z → X × S → ℂ) (hf : ∀ p, Continuous fun z => f z p) (K : Set S) :
    {x : X | ∀ s ∈ K, ∃ z, f z (x, s) ≠ 0} =
      {x : X | ∀ s ∈ K, ∃ z ∈ Q, f z (x, s) ≠ 0} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h s hs
    exact (exists_ne_zero_iff_exists_mem_dense hQ (fun z => f z (x, s)) (hf (x, s))).1 (h s hs)
  · intro h s hs
    exact (exists_ne_zero_iff_exists_mem_dense hQ (fun z => f z (x, s)) (hf (x, s))).2 (h s hs)

/-- The failure locus described through a dense packet family: at some shift of the patch every
packet of the family degenerates. -/
theorem patchwiseFailure_eq_dense_family
    {X S Z : Type*} [TopologicalSpace Z] {Q : Set Z} (hQ : Dense Q)
    (f : Z → X × S → ℂ) (hf : ∀ p, Continuous fun z => f z p) (K : Set S) :
    patchwiseFailure f K = {x : X | ∃ s ∈ K, ∀ z ∈ Q, f z (x, s) = 0} := by
  have hcompl := setOf_forall_compact_exists_ne_zero_eq_dense_family hQ f hf K
  rw [setOf_forall_compact_exists_ne_zero_eq_compl] at hcompl
  have hset : {x : X | ∀ s ∈ K, ∃ z ∈ Q, f z (x, s) ≠ 0} =
      {x : X | ∃ s ∈ K, ∀ z ∈ Q, f z (x, s) = 0}ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists]
    constructor
    · rintro h s ⟨hs, hall⟩
      obtain ⟨z, hzQ, hz⟩ := h s hs
      exact hz (hall z hzQ)
    · intro h s hs
      by_contra hcon
      push Not at hcon
      exact h s ⟨hs, hcon⟩
  rw [hset] at hcompl
  exact compl_injective hcompl

end

end GaloisForLFunctions.HTGeometry
