import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardStepTwoStruct

/-!
# The conclusion of Grynkiewicz’s theorem, and the element-adjunction device

`PollardConclusion A B t` packages the two alternatives of Grynkiewicz’s theorem.  Two devices
used repeatedly in CASE 4 live here:

* `pollardWeak_of_small_deficiency` — whenever the structural witnesses have deficiency
  `#A′ + #B′ − #(A′·B′) ≤ t`, the weak bound already follows.  This is the mechanism behind
  the source’s repeated “else (weak) would hold” appeals to `|H| − ρ ≥ t + 1`.
* `pollardConclusion_of_insert_left` and `pollardConclusion_of_insert_right` — an element all of
  whose products are already `t`-representable may be adjoined to `A` or to `B` without changing
  any `A ·_i B` with `i ≤ t`; the pair grows by one element at the same `repSum`, which is the
  strictly decreasing second component of the induction measure, and the conclusion descends.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

/-- The conclusion of Grynkiewicz's theorem for a pair `(A, B)`. -/
def PollardConclusion (A B : Finset G) (t : ℕ) : Prop :=
  PollardWeak A B t ∨ PollardStruct A B t

/-- The intermediate bound `∑_{i≤t} #(A ·_i B) ≥ t#A + t#B − t²` implies the weak bound. -/
theorem pollardWeak_of_boundTSq {A B : Finset G} {t : ℕ} (ht : 1 ≤ t)
    (h : t * A.card + t * B.card ≤ repSum A B t + t ^ (2 : ℕ)) : PollardWeak A B t := by
  rw [PollardWeak]
  have : 1 ≤ t ^ (2 : ℕ) := Nat.one_le_pow 2 t ht
  have h2 : t ^ (2 : ℕ) + t ^ (2 : ℕ) = 2 * t ^ (2 : ℕ) := by ring
  omega

theorem pollardConclusion_comm {A B : Finset G} {t : ℕ} (h : PollardConclusion A B t) :
    PollardConclusion B A t :=
  h.imp pollardWeak_comm pollardStruct_comm

/-- **A small deficiency forces the weak bound.**  If `A' · B'` is `t`-representable, the defect is
below `t`, and `#A' + #B' ≤ #(A'·B') + t`, then the weak Pollard bound holds. -/
theorem pollardWeak_of_small_deficiency {A B A' B' : Finset G} {t : ℕ} (ht : 1 ≤ t)
    (hA' : A' ⊆ A) (hB' : B' ⊆ B) (hdef : defect A A' B B' + 1 ≤ t)
    (heq2 : A' * B' ⊆ repSet A B t)
    (hsmall : A'.card + B'.card ≤ (A' * B').card + t) :
    PollardWeak A B t := by
  have h1 : t * (A' * B').card ≤ repSum A B t :=
    le_trans (Nat.mul_le_mul_left t (Finset.card_le_card heq2)) (mul_card_repSet_le_repSum A B t)
  have hcardA := Finset.card_sdiff_add_card_eq_card hA'
  have hcardB := Finset.card_sdiff_add_card_eq_card hB'
  have hexp : t * A.card + t * B.card
      = t * (A'.card + B'.card) + t * defect A A' B B' := by
    rw [← hcardA, ← hcardB]
    simp only [defect]
    ring
  have h2 : t * (A'.card + B'.card) ≤ t * ((A' * B').card + t) := Nat.mul_le_mul_left t hsmall
  have h3 : t * ((A' * B').card + t) = t * (A' * B').card + t * t := by ring
  have h4 : t * defect A A' B B' + t ≤ t * t := by
    have := Nat.mul_le_mul_left t hdef
    have h5 : t * (defect A A' B B' + 1) = t * defect A A' B B' + t := by ring
    omega
  have h6 : t * t = t ^ (2 : ℕ) := by ring
  have h7 : 1 ≤ t ^ (2 : ℕ) := Nat.one_le_pow 2 t ht
  rw [PollardWeak, hexp]
  omega

/-! ### Adjoining a saturated element -/

/-- Adjoining to `A` an element all of whose products with `B` are already `t`-representable does
not change the `i`-representable sets for `i ≤ t`. -/
theorem repSet_insert_left {A B : Finset G} {α : G} {t i : ℕ} (hi : i ≤ t)
    (hrep : ∀ b ∈ B, t ≤ rep A B (α * b)) :
    repSet (insert α A) B i = repSet A B i := by
  classical
  refine Subset.antisymm (fun c hc => ?_) (repSet_mono (Finset.subset_insert α A) Subset.rfl i)
  rw [mem_repSet] at hc ⊢
  by_cases hα : α ∈ A
  · rwa [Finset.insert_eq_self.2 hα] at hc
  · have hrewrite : rep A B c
        = (if α ∈ insert α A ∧ α⁻¹ * c ∈ B then rep (insert α A) B c - 1
            else rep (insert α A) B c) := by
      have h := rep_erase_left (A := insert α A) (a₀ := α) (B := B) c
      rwa [Finset.erase_insert hα] at h
    by_cases hcond : α⁻¹ * c ∈ B
    · have : c = α * (α⁻¹ * c) := by rw [mul_inv_cancel_left]
      rw [this]
      exact le_trans hi (hrep _ hcond)
    · rw [if_neg (fun h => hcond h.2)] at hrewrite
      omega

theorem repSum_insert_left {A B : Finset G} {α : G} {t : ℕ}
    (hrep : ∀ b ∈ B, t ≤ rep A B (α * b)) :
    repSum (insert α A) B t = repSum A B t := by
  rw [repSum, repSum]
  exact Finset.sum_congr rfl (fun i hi => by
    rw [repSet_insert_left (Finset.mem_Icc.1 hi).2 hrep])

theorem repSet_insert_right {A B : Finset G} {α : G} {t i : ℕ} (hi : i ≤ t)
    (hrep : ∀ a ∈ A, t ≤ rep A B (a * α)) :
    repSet A (insert α B) i = repSet A B i := by
  have hrep' : ∀ a ∈ A, t ≤ rep B A (α * a) := by
    intro a ha
    rw [rep_comm B A, mul_comm α a]
    exact hrep a ha
  rw [repSet_comm A (insert α B), repSet_comm A B]
  exact repSet_insert_left hi hrep'

theorem repSum_insert_right {A B : Finset G} {α : G} {t : ℕ}
    (hrep : ∀ a ∈ A, t ≤ rep A B (a * α)) :
    repSum A (insert α B) t = repSum A B t := by
  rw [repSum, repSum]
  exact Finset.sum_congr rfl (fun i hi => by
    rw [repSet_insert_right (Finset.mem_Icc.1 hi).2 hrep])

/-- If nothing is `t`-representable then `repSum` is the full product `#A · #B`, which already
gives the weak bound. -/
theorem pollardWeak_of_repSet_empty {A B : Finset G} {t : ℕ} (ht : 1 ≤ t)
    (hA : t ≤ A.card) (hB : t ≤ B.card) (h : repSet A B t = ∅) : PollardWeak A B t := by
  have hle : ∀ c : G, rep A B c ≤ t := by
    intro c
    by_contra hcon
    have hmem : c ∈ repSet A B t := mem_repSet.2 (by omega)
    rw [h] at hmem
    exact absurd hmem (Finset.notMem_empty c)
  have hval : repSum A B t = A.card * B.card := repSum_eq_of_rep_le A B t hle
  obtain ⟨p, hp⟩ : ∃ p, A.card = t + p := ⟨A.card - t, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q, B.card = t + q := ⟨B.card - t, by omega⟩
  rw [PollardWeak, hval, hp, hq]
  have e1 : (t + p) * (t + q) = t * t + t * q + t * p + p * q := by ring
  have e2 : t * (t + p) + t * (t + q) = 2 * (t * t) + t * p + t * q := by ring
  have e3 : t * t = t ^ (2 : ℕ) := by ring
  have e4 : 1 ≤ t * t := Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

/-- **Adjoining a saturated element on the left.**  If every product `α · b` is already
`t`-representable, the conclusion of Grynkiewicz's theorem descends from `(A ∪ {α}, B)` to
`(A, B)`. -/
theorem pollardConclusion_of_insert_left {A B : Finset G} {α : G} {t : ℕ} (ht : 1 ≤ t)
    (hA : t ≤ A.card) (hB : t ≤ B.card) (hαA : α ∉ A)
    (hrep : ∀ b ∈ B, t ≤ rep A B (α * b))
    (h : PollardConclusion (insert α A) B t) : PollardConclusion A B t := by
  classical
  have hcard : (insert α A).card = A.card + 1 := Finset.card_insert_of_notMem hαA
  have hsum : repSum (insert α A) B t = repSum A B t := repSum_insert_left hrep
  have hset : repSet (insert α A) B t = repSet A B t := repSet_insert_left le_rfl hrep
  rcases h with hw | hs
  · left
    rw [PollardWeak] at hw ⊢
    rw [hcard, hsum] at hw
    have hexp : t * (A.card + 1) = t * A.card + t := by ring
    omega
  obtain ⟨P, Q, hPX, hQsub, hdef, heq1, heq2, hbound⟩ := hs
  rcases le_or_gt (P.card + Q.card) ((P * Q).card + t) with hsmall | hbig
  · left
    have hwX : PollardWeak (insert α A) B t :=
      pollardWeak_of_small_deficiency ht hPX hQsub hdef (le_of_eq heq2) hsmall
    rw [PollardWeak] at hwX ⊢
    rw [hcard, hsum] at hwX
    have hexp : t * (A.card + 1) = t * A.card + t := by ring
    omega
  have hrepbig : ∀ c ∈ P * Q, t + 1 ≤ rep P Q c := by
    intro c hc
    obtain ⟨a, ha, b, hb, _⟩ := mem_mul.1 hc
    have := card_add_card_le_rep_add_card_mul ⟨a, ha⟩ ⟨b, hb⟩ hc
    omega
  have herase : ∀ c ∈ P * Q, t ≤ rep (P.erase α) Q c := by
    intro c hc
    have hre := rep_erase_left (A := P) (a₀ := α) (B := Q) c
    have := hrepbig c hc
    rw [hre]
    split <;> omega
  have hPesub : P.erase α ⊆ A := by
    intro z hz
    have h1 : z ∈ P := Finset.mem_of_mem_erase hz
    have h2 : z ≠ α := Finset.ne_of_mem_erase hz
    rcases Finset.mem_insert.1 (hPX h1) with h | h
    · exact absurd h h2
    · exact h
  have hprodeq : P.erase α * Q = P * Q := by
    refine Subset.antisymm (mul_subset_mul_right (Finset.erase_subset α P)) (fun c hc => ?_)
    exact repSet_subset_mul _ _ ht (mem_repSet.2 (herase c hc))
  have heq1' : repSet (P.erase α) Q t = P.erase α * Q := by
    refine Subset.antisymm (repSet_subset_mul _ _ ht) (fun c hc => ?_)
    rw [hprodeq] at hc
    exact mem_repSet.2 (herase c hc)
  have heq2' : P.erase α * Q = repSet A B t := by rw [hprodeq, heq2, hset]
  have hdef' : defect A (P.erase α) B Q + 1 ≤ t := by
    have h1 : (A \ P.erase α).card + (P.erase α).card = A.card :=
      Finset.card_sdiff_add_card_eq_card hPesub
    have h2 : (insert α A \ P).card + P.card = (insert α A).card :=
      Finset.card_sdiff_add_card_eq_card hPX
    have h3 : P.card ≤ (P.erase α).card + 1 := by
      by_cases hmem : α ∈ P
      · rw [Finset.card_erase_of_mem hmem]
        have : 1 ≤ P.card := Finset.card_pos.2 ⟨α, hmem⟩
        omega
      · rw [Finset.erase_eq_of_notMem hmem]; omega
    rw [defect] at hdef ⊢
    omega
  rcases Finset.eq_empty_or_nonempty (P.erase α) with hPe | hPene
  · left
    refine pollardWeak_of_repSet_empty ht hA hB ?_
    rw [← heq2', hPe, Finset.empty_mul]
  rcases Finset.eq_empty_or_nonempty Q with hQe | hQne
  · left
    refine pollardWeak_of_repSet_empty ht hA hB ?_
    rw [← heq2', hQe, Finset.mul_empty]
  rcases pollard_step1 A B (P.erase α) Q t ht hPesub hQsub hPene hQne hdef' heq1' heq2' with h | h
  · exact Or.inr h
  · exact Or.inl (pollardWeak_of_boundTSq ht h)

/-- **Adjoining a saturated element on the right.** -/
theorem pollardConclusion_of_insert_right {A B : Finset G} {α : G} {t : ℕ} (ht : 1 ≤ t)
    (hA : t ≤ A.card) (hB : t ≤ B.card) (hαB : α ∉ B)
    (hrep : ∀ a ∈ A, t ≤ rep A B (a * α))
    (h : PollardConclusion A (insert α B) t) : PollardConclusion A B t := by
  have hrep' : ∀ a ∈ A, t ≤ rep B A (α * a) := by
    intro a ha
    rw [rep_comm B A, mul_comm α a]
    exact hrep a ha
  exact pollardConclusion_comm
    (pollardConclusion_of_insert_left ht hB hA hαB hrep' (pollardConclusion_comm h))

end GaloisForLFunctions.HTGeometry.AddComb
