import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardStepOneMain
import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardStepTwo
import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardDeletion

/-!
# STEP 2 of Grynkiewicz's proof, structural branch

STEP 2 supposes that deleting one point `y` of `B` (or of `A`) lowers `∑_{i≤t} #(A ·_i B)` by at
least `t`.  The weak branch is `pollardWeak_of_erase_right`; this file proves the structural
branch, `pollard_step2_struct`, which runs the STEP 1 machinery on the saturated witnesses.

The three ingredients are:

* `rep_le_defect_of_notMem` — outside `A' · B'` a product has at most `#(A \ A') + #(B \ B')`
  representations, so a defect of at most `t − 2` forces `A ·_t B = A ·_t (B \ y)`;
* `repSum_le_repSum_erase_add` — the deletion cost is confined to the translate `y · A`, which is
  what rules out `y ∈ B' · H`;
* the relaxation of `pollard_step1_smallDoubling` to a defect equal to `t`, where its conclusion
  degenerates to `∑_{i≤t} #(A ·_i B) ≥ t#A + t#B − t²`.

Both sides of the deletion are covered, `pollard_step2_struct` and `pollard_step2_struct_left`,
using the symmetry `pollardStruct_comm`.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

omit [Fintype G] in
/-- Representation counts split over a partition of the first factor. -/
theorem rep_sdiff_add_rep {A A' : Finset G} (hA' : A' ⊆ A) (B : Finset G) (c : G) :
    rep A B c = rep (A \ A') B c + rep A' B c := by
  classical
  rw [rep_eq_card_inter, rep_eq_card_inter, rep_eq_card_inter]
  have hdisj : Disjoint ((A \ A') ∩ (c • B⁻¹)) (A' ∩ (c • B⁻¹)) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    exact (Finset.mem_sdiff.1 (Finset.mem_inter.1 hz).1).2 (Finset.mem_inter.1 hz').1
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext z
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hz, hs⟩
    by_cases h : z ∈ A'
    · exact Or.inr ⟨h, hs⟩
    · exact Or.inl ⟨⟨hz, h⟩, hs⟩
  · rintro (⟨⟨hz, _⟩, hs⟩ | ⟨hz, hs⟩)
    · exact ⟨hz, hs⟩
    · exact ⟨hA' hz, hs⟩

omit [Fintype G] in
/-- Outside `A' · B'`, every product has at most `defect` representations in `A × B`. -/
theorem rep_le_defect_of_notMem {A A' B B' : Finset G} (hA' : A' ⊆ A) (hB' : B' ⊆ B)
    {c : G} (hc : c ∉ A' * B') : rep A B c ≤ defect A A' B B' := by
  classical
  have h1 : rep A B c = rep (A \ A') B c + rep A' B c := rep_sdiff_add_rep hA' B c
  have h2 : rep A' B c = rep A' (B \ B') c + rep A' B' c := by
    rw [rep_comm A' B, rep_comm A' (B \ B'), rep_comm A' B']
    exact rep_sdiff_add_rep hB' A' c
  have h3 : rep A' B' c = 0 := by
    by_contra h
    exact hc ((rep_pos_iff_mem_mul A' B' c).1 (Nat.pos_of_ne_zero h))
  have h4 := rep_le_card_left (A \ A') B c
  have h5 := rep_le_card_right A' (B \ B') c
  rw [defect]
  omega

omit [Fintype G] in
/-- Deleting one point of `B` lowers a representation count by at most one. -/
theorem rep_le_rep_erase_succ (A B : Finset G) (y : G) (c : G) :
    rep A B c ≤ rep A (B.erase y) c + 1 := by
  classical
  have h : rep A (B.erase y) c
      = (if y ∈ B ∧ y⁻¹ * c ∈ A then rep A B c - 1 else rep A B c) := by
    rw [rep_comm A (B.erase y), rep_erase_left c, rep_comm B A]
  rw [h]
  split <;> omega

/-- **The deletion cost is confined to one translate.**  Removing `y` from `B` lowers `repSum` by
at most the number of elements of `y · A` that are not already `t`-representable in `A × (B \ y)`.
-/
theorem repSum_le_repSum_erase_add (A B : Finset G) (t : ℕ) (y : G) :
    repSum A B t ≤ repSum A (B.erase y) t
      + ((y • A).filter (fun c => rep A (B.erase y) c < t)).card := by
  classical
  have hmemsm : ∀ c : G, c ∈ y • A ↔ y⁻¹ * c ∈ A := by
    intro c
    rw [Finset.mem_smul_finset]
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro h
      exact ⟨y⁻¹ * c, h, by simp [smul_eq_mul, mul_inv_cancel_left]⟩
  have hcard : ((y • A).filter (fun c => rep A (B.erase y) c < t)).card
      = ∑ c : G, (if c ∈ y • A ∧ rep A (B.erase y) c < t then 1 else 0) := by
    rw [← Finset.card_filter]
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [repSum_eq_sum_min, repSum_eq_sum_min, hcard, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun c _ => ?_)
  have h : rep A (B.erase y) c
      = (if y ∈ B ∧ y⁻¹ * c ∈ A then rep A B c - 1 else rep A B c) := by
    rw [rep_comm A (B.erase y), rep_erase_left c, rep_comm B A]
  by_cases hcond : y ∈ B ∧ y⁻¹ * c ∈ A
  · have hpos : 1 ≤ rep A B c := by
      rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, rep_pos_iff_mem_mul]
      exact mem_mul.2 ⟨y⁻¹ * c, hcond.2, y, hcond.1, by rw [mul_comm, mul_inv_cancel_left]⟩
    rw [if_pos hcond] at h
    by_cases hlt : rep A (B.erase y) c < t
    · rw [if_pos ⟨(hmemsm c).2 hcond.2, hlt⟩]
      omega
    · rw [if_neg (fun hh => hlt hh.2)]
      omega
  · rw [if_neg hcond] at h
    omega

/-- **STEP 2, structural branch.**  If deleting `y ∈ B` drops `repSum` by at least `t` and the
structural alternative holds for `(A, B \ y)`, then the conclusion of Grynkiewicz's theorem holds
for `(A, B)`. -/
theorem pollard_step2_struct (A B A' B' : Finset G) (t : ℕ) (ht : 1 ≤ t) {y : G} (hy : y ∈ B)
    (hA' : A' ⊆ A) (hB' : B' ⊆ B.erase y) (hA'ne : A'.Nonempty) (hB'ne : B'.Nonempty)
    (hl : defect A A' (B.erase y) B' + 1 ≤ t)
    (heq1 : repSet A' B' t = A' * B')
    (heq2 : A' * B' = repSet A (B.erase y) t)
    (hdrop : repSum A (B.erase y) t + t ≤ repSum A B t) :
    PollardStruct A B t ∨ (t * A.card + t * B.card ≤ repSum A B t + t ^ (2 : ℕ)) := by
  classical
  set A'' := satur A A' B' with hA''def
  set B'' := satur (B.erase y) B' A' with hB''def
  have hprod : A'' * B'' = A' * B' := satur_mul_satur A A' (B.erase y) B'
  have hA''sub : A'' ⊆ A := satur_subset hA'
  have hB''sub : B'' ⊆ B.erase y := satur_subset hB'
  have hB''subB : B'' ⊆ B := hB''sub.trans (Finset.erase_subset y B)
  have hA''ne : A''.Nonempty := hA'ne.mono (subset_satur A A' B')
  have hB''ne : B''.Nonempty := hB'ne.mono (subset_satur (B.erase y) B' A')
  have hdef'' : defect A A'' (B.erase y) B'' + 1 ≤ t := by
    have hle := defect_satur_le A A' (B.erase y) B'
    rw [← hA''def, ← hB''def] at hle
    omega
  have heq2'' : A'' * B'' = repSet A (B.erase y) t := by rw [hprod, heq2]
  have heq1'' : repSet A'' B'' t = A'' * B'' := by
    refine Subset.antisymm (repSet_subset_mul A'' B'' ht) ?_
    rw [hprod, ← heq1]
    exact repSet_mono (subset_satur A A' B') (subset_satur (B.erase y) B' A') t
  have hsubBt : A'' * B'' ⊆ repSet A B t := by
    rw [heq2'']
    exact repSet_mono Subset.rfl (Finset.erase_subset y B) t
  have hcardB : B.card = (B.erase y).card + 1 := by
    rw [Finset.card_erase_of_mem hy]
    have : 1 ≤ B.card := Finset.card_pos.2 ⟨y, hy⟩
    omega
  rcases le_or_gt (A''.card + B''.card) ((A'' * B'').card + 1) with hlarge | hsmall
  · right
    have hmain := pollard_step1_largeProduct A (B.erase y) A'' B'' t hA''sub hB''sub hdef''
      (le_of_eq heq2'') hlarge
    have hexp : t * ((B.erase y).card + 1) = t * (B.erase y).card + t := by ring
    rw [hcardB]
    omega
  -- the deleted point does not lie in `B'' · H`
  have hsatA : ∀ x ∈ A, x ∈ A'' * mulStab (A'' * B'') → x ∈ A'' :=
    satur_saturated A A' (B.erase y) B'
  have hsatB0 : ∀ z ∈ B.erase y, z ∈ B'' * mulStab (A'' * B'') → z ∈ B'' := by
    have h := satur_saturated (B.erase y) B' A A'
    intro z hz hmem
    apply h z hz
    have hcomm : satur (B.erase y) B' A' * satur A A' B' = A'' * B'' := by
      rw [hA''def, hB''def, mul_comm]
    rw [hcomm]
    exact hmem
  have hyH : y ∉ B'' * mulStab (A'' * B'') := by
    intro hcon
    have hkey : ∀ a ∈ A'', t ≤ rep A (B.erase y) (y * a) := by
      intro a ha
      have h1 : a * y ∈ A'' * (B'' * mulStab (A'' * B'')) := Finset.mul_mem_mul ha hcon
      rw [← mul_assoc, mul_mulStab, heq2'', mem_repSet] at h1
      rw [mul_comm y a]
      exact h1
    have hsub : (y • A).filter (fun c => rep A (B.erase y) c < t) ⊆ (y • A) \ (y • A'') := by
      intro c hc
      rw [Finset.mem_filter] at hc
      refine Finset.mem_sdiff.2 ⟨hc.1, ?_⟩
      intro hcon2
      obtain ⟨a, ha, rfl⟩ := Finset.mem_smul_finset.1 hcon2
      have := hkey a ha
      simp only [smul_eq_mul] at hc
      omega
    have hcard : ((y • A).filter (fun c => rep A (B.erase y) c < t)).card ≤ (A \ A'').card := by
      have hss : y • A'' ⊆ y • A := Finset.smul_finset_subset_smul_finset hA''sub
      have h1 : ((y • A) \ (y • A'')).card + (y • A'').card = (y • A).card :=
        Finset.card_sdiff_add_card_eq_card hss
      have h2 : (A \ A'').card + A''.card = A.card :=
        Finset.card_sdiff_add_card_eq_card hA''sub
      have h3 : (y • A).card = A.card := Finset.card_smul_finset y A
      have h4 : (y • A'').card = A''.card := Finset.card_smul_finset y A''
      have h5 := Finset.card_le_card hsub
      omega
    have hup := repSum_le_repSum_erase_add A B t y
    have hdefA : (A \ A'').card ≤ defect A A'' (B.erase y) B'' := by
      rw [defect]; omega
    omega
  have hsatB : ∀ z ∈ B, z ∈ B'' * mulStab (A'' * B'') → z ∈ B'' := by
    intro z hz hmem
    by_cases hzy : z = y
    · exact absurd (hzy ▸ hmem) hyH
    · exact hsatB0 z (Finset.mem_erase.2 ⟨hzy, hz⟩) hmem
  -- the defect grows by exactly one when `y` is put back
  have hdefstep : defect A A'' B B'' = defect A A'' (B.erase y) B'' + 1 := by
    have hyB'' : y ∉ B'' := fun h => (Finset.mem_erase.1 (hB''sub h)).1 rfl
    have hE : (B \ B'').erase y = (B.erase y) \ B'' := by
      ext z
      simp only [Finset.mem_erase, Finset.mem_sdiff]
      tauto
    have hmem : y ∈ B \ B'' := Finset.mem_sdiff.2 ⟨hy, hyB''⟩
    have := Finset.card_erase_of_mem hmem
    rw [hE] at this
    have hpos : 1 ≤ (B \ B'').card := Finset.card_pos.2 ⟨y, hmem⟩
    rw [defect, defect]
    omega
  rcases le_or_gt (defect A A'' (B.erase y) B'' + 2) t with hsmalldef | hbigdef
  · -- the defect is still small enough for STEP 1 applied to `(A, B)`
    have hrepEq : A'' * B'' = repSet A B t := by
      refine Subset.antisymm hsubBt (fun c hc => ?_)
      by_contra hcon
      have h1 := rep_le_defect_of_notMem hA''sub hB''sub hcon
      have h2 := rep_le_rep_erase_succ A B y c
      rw [mem_repSet] at hc
      omega
    exact pollard_step1 A B A'' B'' t ht hA''sub hB''subB hA''ne hB''ne (by omega) heq1'' hrepEq
  · right
    have hdd : defect A A'' B B'' = t := by omega
    have hmain := pollard_step1_smallDoubling A B A'' B'' t hA''sub hB''subB hA''ne hB''ne
      (by omega) hsubBt (by omega) hsatA hsatB
    rw [hdd, Nat.sub_self] at hmain
    have hsq : t * t = t ^ (2 : ℕ) := by ring
    omega

/-! ### Symmetry of the two conclusions -/

theorem repSet_comm (A B : Finset G) (i : ℕ) : repSet A B i = repSet B A i := by
  ext c
  simp only [mem_repSet]
  rw [rep_comm]

theorem pollardWeak_comm {A B : Finset G} {t : ℕ} (h : PollardWeak A B t) : PollardWeak B A t := by
  rw [PollardWeak] at h ⊢
  rw [repSum_comm B A]
  omega

theorem pollardStruct_comm {A B : Finset G} {t : ℕ} (h : PollardStruct A B t) :
    PollardStruct B A t := by
  obtain ⟨A', B', hA', hB', hdef, h1, h2, h3⟩ := h
  refine ⟨B', A', hB', hA', ?_, ?_, ?_, ?_⟩
  · rw [defect] at hdef ⊢; omega
  · rw [repSet_comm B' A', mul_comm B' A']; exact h1
  · rw [mul_comm B' A', repSet_comm B A]; exact h2
  · have hdefeq : defect B B' A A' = defect A A' B B' := by rw [defect, defect]; omega
    have hholes : holes (mulStab (repSet B A t)) B' A' = holes (mulStab (repSet A B t)) A' B' := by
      rw [repSet_comm B A, holes, holes]; omega
    rw [hdefeq, hholes, repSet_comm B A, repSum_comm B A]
    omega

/-- **STEP 2, structural branch, first factor.** -/
theorem pollard_step2_struct_left (A B A' B' : Finset G) (t : ℕ) (ht : 1 ≤ t) {y : G} (hy : y ∈ A)
    (hA' : A' ⊆ A.erase y) (hB' : B' ⊆ B) (hA'ne : A'.Nonempty) (hB'ne : B'.Nonempty)
    (hl : defect (A.erase y) A' B B' + 1 ≤ t)
    (heq1 : repSet A' B' t = A' * B')
    (heq2 : A' * B' = repSet (A.erase y) B t)
    (hdrop : repSum (A.erase y) B t + t ≤ repSum A B t) :
    PollardStruct A B t ∨ (t * A.card + t * B.card ≤ repSum A B t + t ^ (2 : ℕ)) := by
  have hdrop' : repSum B (A.erase y) t + t ≤ repSum B A t := by
    rw [repSum_comm B (A.erase y), repSum_comm B A]; exact hdrop
  have hmain := pollard_step2_struct B A B' A' t ht hy hB' hA' hB'ne hA'ne
    (by rw [defect] at hl ⊢; omega)
    (by rw [repSet_comm B' A', mul_comm B' A']; exact heq1)
    (by rw [mul_comm B' A', repSet_comm B (A.erase y)]; exact heq2) hdrop'
  rcases hmain with h | h
  · exact Or.inl (pollardStruct_comm h)
  · right
    rw [repSum_comm B A] at h
    omega

end GaloisForLFunctions.HTGeometry.AddComb
