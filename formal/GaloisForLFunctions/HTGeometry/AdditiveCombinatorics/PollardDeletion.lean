import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardStepTwo

/-!
# Deletion costs and stabiliser invariance

Two ingredients of Grynkiewicz's induction beyond STEP 1.

* `rep_smul_mulStab`: representation counts are invariant under translating by the stabiliser of
  the first set, so `A ·_i B` is a union of `S(A)`-cosets.  This is what forces `#S(A) ≤ t − 1` in
  the source's argument.
* `repSum_erase_left_add_le` / `repSum_erase_right_add_le`: deleting a point `a₀ ∈ A` costs
  `repSum` one unit for every element of `a₀ · B` with at most `t` representations.  Combined in
  `exists_erase_drop`, this is the "unstuff" pigeonhole: once the two costs together reach
  `2t − 1`, one deletion drops `repSum` by at least `t`, which is exactly the hypothesis of
  STEP 2.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

/-- Representation counts are invariant under translation by the stabiliser of the first set. -/
theorem rep_smul_mulStab {A B : Finset G} {h : G} (hh : h ∈ mulStab A) (c : G) :
    rep A B (h * c) = rep A B c := by
  classical
  rw [rep_eq_card_inter, rep_eq_card_inter]
  have hA : h • A = A := mem_mulStab.1 hh
  have hsm : (h * c) • B⁻¹ = h • (c • B⁻¹) := by rw [mul_smul]
  rw [hsm, ← hA, ← Finset.smul_finset_inter, Finset.card_smul_finset, hA]

theorem mem_repSet_smul_mulStab {A B : Finset G} {h : G} (hh : h ∈ mulStab A) (i : ℕ) (c : G) :
    h * c ∈ repSet A B i ↔ c ∈ repSet A B i := by
  rw [mem_repSet, mem_repSet, rep_smul_mulStab hh]

omit [Fintype G] in
/-- Deleting one point of `A` changes the representation count in the expected way. -/
theorem rep_erase_left {A B : Finset G} {a₀ : G} (c : G) :
    rep (A.erase a₀) B c
      = (if a₀ ∈ A ∧ a₀⁻¹ * c ∈ B then rep A B c - 1 else rep A B c) := by
  classical
  rw [rep_eq_card_filter_left, rep_eq_card_filter_left]
  have hfe : (A.erase a₀).filter (fun x => x⁻¹ * c ∈ B)
      = (A.filter (fun x => x⁻¹ * c ∈ B)).erase a₀ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  rw [hfe]
  by_cases h : a₀ ∈ A ∧ a₀⁻¹ * c ∈ B
  · rw [if_pos h, Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨h.1, h.2⟩)]
  · rw [if_neg h, Finset.erase_eq_of_notMem]
    intro hmem
    exact h ⟨(Finset.mem_filter.1 hmem).1, (Finset.mem_filter.1 hmem).2⟩

/-- **The cost of deleting a point of `A`.**  Every element of `a₀ · B` with at most `t`
representations costs one unit of `repSum` when `a₀` is removed. -/
theorem repSum_erase_left_add_le (A B : Finset G) (t : ℕ) {a₀ : G} (ha₀ : a₀ ∈ A) :
    repSum (A.erase a₀) B t + ((a₀ • B).filter (fun c => rep A B c ≤ t)).card
      ≤ repSum A B t := by
  classical
  have hmemsm : ∀ c : G, c ∈ a₀ • B ↔ a₀⁻¹ * c ∈ B := by
    intro c
    rw [Finset.mem_smul_finset]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro h
      exact ⟨a₀⁻¹ * c, h, by simp [smul_eq_mul, mul_inv_cancel_left]⟩
  have hcard : ((a₀ • B).filter (fun c => rep A B c ≤ t)).card
      = ∑ c : G, (if c ∈ a₀ • B ∧ rep A B c ≤ t then 1 else 0) := by
    rw [← Finset.card_filter]
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [repSum_eq_sum_min, repSum_eq_sum_min, hcard, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun c _ => ?_)
  rw [rep_erase_left c]
  by_cases hc : a₀⁻¹ * c ∈ B
  · have hcond : (a₀ ∈ A ∧ a₀⁻¹ * c ∈ B) := ⟨ha₀, hc⟩
    have hpos : 1 ≤ rep A B c := by
      rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, rep_pos_iff_mem_mul]
      exact mem_mul.2 ⟨a₀, ha₀, a₀⁻¹ * c, hc, by rw [mul_inv_cancel_left]⟩
    rw [if_pos hcond]
    by_cases hle : rep A B c ≤ t
    · rw [if_pos ⟨(hmemsm c).2 hc, hle⟩]
      omega
    · rw [if_neg (fun h => hle h.2)]
      omega
  · have hcond : ¬ (a₀ ∈ A ∧ a₀⁻¹ * c ∈ B) := fun h => hc h.2
    have hcond2 : ¬ (c ∈ a₀ • B ∧ rep A B c ≤ t) := by
      intro h
      exact hc ((hmemsm c).1 h.1)
    rw [if_neg hcond, if_neg hcond2]
    omega


theorem repSum_comm (A B : Finset G) (t : ℕ) : repSum A B t = repSum B A t := by
  rw [repSum_eq_sum_min, repSum_eq_sum_min]
  exact Finset.sum_congr rfl (fun c _ => by rw [rep_comm])

/-- **The cost of deleting a point of `B`.** -/
theorem repSum_erase_right_add_le (A B : Finset G) (t : ℕ) {b₀ : G} (hb₀ : b₀ ∈ B) :
    repSum A (B.erase b₀) t + ((b₀ • A).filter (fun c => rep A B c ≤ t)).card
      ≤ repSum A B t := by
  have h := repSum_erase_left_add_le B A t hb₀
  rw [repSum_comm (B.erase b₀) A, repSum_comm B A] at h
  have hfil : ((b₀ • A).filter (fun c => rep B A c ≤ t)).card
      = ((b₀ • A).filter (fun c => rep A B c ≤ t)).card := by
    congr 1
    apply Finset.filter_congr
    intro c _
    rw [rep_comm]
  rw [hfil] at h
  exact h

/-- **The unstuff pigeonhole.**  If the two deletion costs together reach `2t − 1`, then deleting
one of the two points drops `repSum` by at least `t`, which is the hypothesis of STEP 2. -/
theorem exists_erase_drop (A B : Finset G) (t : ℕ) {a₀ b₀ : G} (ha₀ : a₀ ∈ A) (hb₀ : b₀ ∈ B)
    (hbig : 2 * t ≤ ((a₀ • B).filter (fun c => rep A B c ≤ t)).card
      + ((b₀ • A).filter (fun c => rep A B c ≤ t)).card + 1) :
    (repSum (A.erase a₀) B t + t ≤ repSum A B t)
      ∨ (repSum A (B.erase b₀) t + t ≤ repSum A B t) := by
  rcases le_or_gt t ((a₀ • B).filter (fun c => rep A B c ≤ t)).card with hL | hL
  · left
    have := repSum_erase_left_add_le A B t ha₀
    omega
  · right
    have hR : t ≤ ((b₀ • A).filter (fun c => rep A B c ≤ t)).card := by omega
    have := repSum_erase_right_add_le A B t hb₀
    omega

end GaloisForLFunctions.HTGeometry.AddComb
