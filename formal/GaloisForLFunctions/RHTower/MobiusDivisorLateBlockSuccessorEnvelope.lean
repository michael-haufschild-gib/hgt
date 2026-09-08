import GaloisForLFunctions.RHTower.MobiusDivisorSuccessorAverageObstruction

/-!
# Endpoint control of the complete successor envelope through late blocks

The actual energy of an isolated late-prime block is bounded by its two
endpoints at every intermediate subset. This remains true simultaneously
for every unprocessed successor: a successor outside the block uses the
same endpoint law at its enlarged starting core; a successor inside the
block is another intermediate subset. Thus the full successor envelope
has an endpoint bound without an additive cost for each merger.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace RHTower

/-- Every intermediate subset of an unprocessed late-prime block has
successor envelope bounded by the two endpoint envelopes. All remaining
successors are retained, including primes still inside the block. -/
theorem mobiusDivisorSuccessorEnvelope_late_block_le_max_endpoints
    (M : ℕ) (P L R : Finset ℕ)
    (hL : ∀p∈L,p.Prime ∧ p<M ∧ M≤2*p) (hfree : ∀p∈L,p∉P) (hRL : R⊆L) :
    mobiusDivisorSuccessorEnvelope M (P∪R)≤
      max (mobiusDivisorSuccessorEnvelope M P) (mobiusDivisorSuccessorEnvelope M (P∪L)) := by
  have hbase := (mobiusDivisorSuccessorEnvelope_le_iff M P _).mp le_rfl
  have hend := (mobiusDivisorSuccessorEnvelope_le_iff M (P∪L) _).mp le_rfl
  have hcurrent (S : Finset ℕ) (hS : S⊆L) :
      mobiusDivisorSelectionEnergy M (P∪S)≤
        max (mobiusDivisorSuccessorEnvelope M P) (mobiusDivisorSuccessorEnvelope M (P∪L)) :=
    (mobiusDivisorSelectionEnergy_late_block_le_max_endpoints M P L S hL hfree hS).trans
      (max_le_max hbase.1 hend.1)
  rw [mobiusDivisorSuccessorEnvelope_le_iff]
  refine ⟨hcurrent R hRL,?_⟩
  intro q hq
  obtain ⟨hqactive,hqnot⟩ := mem_sdiff.mp hq
  have hqP : q∉P := fun h => hqnot (mem_union_left R h)
  by_cases hqL : q∈L
  · have hS : insert q R⊆L := insert_subset_iff.mpr ⟨hqL,hRL⟩
    simpa only [union_insert] using hcurrent (insert q R) hS
  · have hqend : q∉P∪L := by simp [hqP,hqL]
    have hfreeq : ∀p∈L,p∉insert q P := by
      intro p hp
      simp only [mem_insert,not_or]
      exact ⟨fun he => hqL (he ▸ hp),hfree p hp⟩
    have hb := mobiusDivisorSelectionEnergy_late_block_le_max_endpoints M
      (insert q P) L R hL hfreeq hRL
    have hleft := hbase.2 q (mem_sdiff.mpr ⟨hqactive,hqP⟩)
    have hright := hend.2 q (mem_sdiff.mpr ⟨hqactive,hqend⟩)
    simp only [insert_union] at hb
    exact hb.trans (max_le_max hleft hright)

end RHTower
