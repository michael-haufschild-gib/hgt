import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardDysonWitness

/-!
# The stabiliser of the first set is small

`repSet_eq_or_exists_erase_drop`: if `#S(A) ≥ t`, then either `A · B = A ·_t B` — putting one in
the situation of STEP 1 with `A' = A`, `B' = B` — or some `b ∈ B` costs at least `t` to delete,
which is the hypothesis of STEP 2.

The mechanism is `rep_smul_mulStab`: representation counts are constant on `S(A)`-cosets, so a
single cheap product `a · b` drags its whole `S(A)`-coset along, and that coset sits inside
`b · A`.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

/-- **The stabiliser of `A` is small.**  If `#S(A) ≥ t` then either every product is already
`t`-representable — the hypothesis of STEP 1 with `A' = A`, `B' = B` — or some point of `B` is
expensive enough for STEP 2. -/
theorem repSet_eq_or_exists_erase_drop (A B : Finset G) (t : ℕ) (ht : 1 ≤ t)
    (hbig : t ≤ (mulStab A).card) :
    (A * B = repSet A B t) ∨ ∃ b ∈ B, repSum A (B.erase b) t + t ≤ repSum A B t := by
  classical
  by_cases hall : ∀ c ∈ A * B, t + 1 ≤ rep A B c
  · left
    refine Subset.antisymm (fun c hc => ?_) (repSet_subset_mul A B ht)
    rw [mem_repSet]
    have := hall c hc
    omega
  · right
    push Not at hall
    obtain ⟨c, hc, hlt⟩ := hall
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_mul.1 hc
    refine ⟨b, hb, ?_⟩
    have hcost := repSum_erase_right_add_le A B t hb
    have hsub : (a * b) • mulStab A ⊆ (b • A).filter (fun z => rep A B z ≤ t) := by
      intro z hz
      rw [Finset.mem_smul_finset] at hz
      obtain ⟨h, hh, rfl⟩ := hz
      have hhA : h * a ∈ A := by
        have hstab : h • A = A := mem_mulStab.1 hh
        have : h • a ∈ h • A := Finset.smul_mem_smul_finset ha
        rw [hstab] at this
        simpa using this
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_smul_finset]
        refine ⟨h * a, hhA, ?_⟩
        simp only [smul_eq_mul]
        simp [mul_comm, mul_left_comm]
      · simp only [smul_eq_mul]
        have hcomm : (a * b) * h = h * (a * b) := mul_comm _ _
        rw [hcomm, rep_smul_mulStab hh]
        omega
    have hcard : (mulStab A).card ≤ ((b • A).filter (fun z => rep A B z ≤ t)).card := by
      calc (mulStab A).card = ((a * b) • mulStab A).card :=
            (Finset.card_smul_finset (a * b) _).symm
        _ ≤ _ := Finset.card_le_card hsub
    omega

end GaloisForLFunctions.HTGeometry.AddComb
