import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardCaseFourTwo

/-!
# CASE 4.2 of Grynkiewicz’s proof: the mixed cosets vanish

With `X = A ∪ B`, `Y = A ∩ B` and `H = S(X · Y)` periodic for `Y`, the maximality of the Dyson
witness rules out a coset of `H` meeting both `A ∖ B` and `B` as soon as some other coset meets
`B` but not `A` (`case42_no_mixed_coset`).  Consequently every coset of `H` is of one of three
kinds: contained in `Y`, meeting only `A`, or meeting only `B`.  Comparing the two mixed kinds
then forces either the whole product set to be `t`-representable — where STEP 1 finishes — or
two nearly empty cosets, whose holes contradict `#H − ρ ≥ t + 1` (`case42_step3`).
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

omit [Fintype G] in
theorem dysonSmall_one (A B : Finset G) : dysonSmall A B 1 = B ∩ A := by
  rw [dysonSmall, one_smul]

omit [Fintype G] in
theorem dysonLarge_one (A B : Finset G) : dysonLarge A B 1 = B ∪ A := by
  rw [dysonLarge, one_smul]

omit [Fintype G] in
/-- A periodic set contains the whole coset of each of its points. -/
theorem coset_subset_of_periodic {S H : Finset G} (hper : S * H = S) {y : G} (hy : y ∈ S) :
    y • H ⊆ S := by
  intro z hz
  obtain ⟨h, hh, rfl⟩ := Finset.mem_smul_finset.1 hz
  rw [← hper]
  exact Finset.mul_mem_mul hy hh

omit [Fintype G] in
/-- **The full-translate consequence of maximality.**  If a coset of `H` meets both `A ∖ B` and
`B`, the corresponding translation carries all of `B` into `A`. -/
theorem dysonSmall_full_of_mixed {A B H : Finset G} (hH : IsSubgroupFinset H)
    (hper : (A ∩ B) * H = A ∩ B)
    (hmax : ∀ z : G, (dysonSmall A B z).Nonempty → (dysonSmall A B z).card < B.card →
        (dysonSmall A B z).card ≤ (dysonSmall A B 1).card)
    {a b : G} (haA : a ∈ A) (haB : a ∉ B) (hbB : b ∈ B) (hbcoset : b ∈ a • H) :
    (a * b⁻¹) • B ⊆ A := by
  classical
  set y := a * b⁻¹ with hydef
  have hyH : y ∈ H := by
    have h1 : a⁻¹ * b ∈ H := mem_smul_finset_iff.1 hbcoset
    have h2 : (a⁻¹ * b)⁻¹ ∈ H := hH.inv_mem h1
    simpa [hydef, mul_comm] using h2
  have hyinv : y⁻¹ ∈ H := hH.inv_mem hyH
  have hYsub : A ∩ B ⊆ dysonSmall A B y := subset_dysonSmall_of_periodic hper hyinv
  have hay : a ∈ dysonSmall A B y := by
    refine Finset.mem_inter.2 ⟨mem_smul_finset_iff.2 ?_, haA⟩
    have hya : y⁻¹ * a = b := by
      rw [hydef, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
    rw [hya]
    exact hbB
  have hanotY : a ∉ A ∩ B := fun h => haB (Finset.mem_inter.1 h).2
  have hbig : (A ∩ B).card + 1 ≤ (dysonSmall A B y).card := by
    have hsub : insert a (A ∩ B) ⊆ dysonSmall A B y := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hay
      · exact hYsub hz
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hanotY] at this
    omega
  have hone : (dysonSmall A B 1).card = (A ∩ B).card := by
    rw [dysonSmall_one, Finset.inter_comm]
  rcases lt_or_ge (dysonSmall A B y).card B.card with hlt | hge
  · have := hmax y ⟨a, hay⟩ hlt
    omega
  have hfull : dysonSmall A B y = y • B := by
    refine Finset.eq_of_subset_of_card_le Finset.inter_subset_left ?_
    rw [Finset.card_smul_finset]
    exact hge
  rw [← hfull]
  exact Finset.inter_subset_right

omit [Fintype G] in
/-- **CASE 4.2, step 3a.**  If some coset of `H` meets both `A ∖ B` and `B`, while some other
coset meets `B` but not `A`, the maximality of the Dyson witness is violated. -/
theorem case42_no_mixed_coset {A B H : Finset G} (hH : IsSubgroupFinset H)
    (hper : (A ∩ B) * H = A ∩ B)
    (hmax : ∀ z : G, (dysonSmall A B z).Nonempty → (dysonSmall A B z).card < B.card →
        (dysonSmall A B z).card ≤ (dysonSmall A B 1).card)
    {b₁ : G} (hb₁ : b₁ ∈ B) (hb₁H : ∀ z ∈ A, z ∉ b₁ • H)
    {a b : G} (haA : a ∈ A) (haB : a ∉ B) (hbB : b ∈ B) (hbcoset : b ∈ a • H) :
    False := by
  classical
  have hsubA := dysonSmall_full_of_mixed hH hper hmax haA haB hbB hbcoset
  have hyH : a * b⁻¹ ∈ H := by
    have h1 : a⁻¹ * b ∈ H := mem_smul_finset_iff.1 hbcoset
    have h2 : (a⁻¹ * b)⁻¹ ∈ H := hH.inv_mem h1
    simpa [mul_comm] using h2
  have hmem : (a * b⁻¹) * b₁ ∈ A := hsubA (Finset.mem_smul_finset.2 ⟨b₁, hb₁, rfl⟩)
  refine hb₁H _ hmem (mem_smul_finset_iff.2 ?_)
  have hcalc : b₁⁻¹ * ((a * b⁻¹) * b₁) = a * b⁻¹ := by
    rw [mul_comm (a * b⁻¹) b₁, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hcalc]
  exact hyH

omit [Fintype G] in
/-- Inside a coset pair, the convolution bound turns a card condition into `t` representations. -/
theorem t_le_rep_of_coset {A B H : Finset G} (hH : IsSubgroupFinset H) {t : ℕ} {a b : G}
    (hcard : H.card + t ≤ (A ∩ (a • H)).card + (B ∩ (b • H)).card) :
    t ≤ rep A B (a * b) := by
  have hcos := card_add_card_le_rep_add_card_coset hH
    (Finset.inter_subset_right : A ∩ (a • H) ⊆ a • H)
    (Finset.inter_subset_right : B ∩ (b • H) ⊆ b • H)
    (hH.mem_smul_self (a * b))
  have hmono := rep_mono (Finset.inter_subset_left : A ∩ (a • H) ⊆ A)
    (Finset.inter_subset_left : B ∩ (b • H) ⊆ B) (a * b)
  omega

omit [Fintype G] in
/-- A point of the periodic part has a full coset slice. -/
theorem card_inter_coset_of_mem_periodic {A B H : Finset G}
    (hper : (A ∩ B) * H = A ∩ B) {z : G} (hz : z ∈ A ∩ B) :
    (A ∩ (z • H)).card = H.card ∧ (B ∩ (z • H)).card = H.card := by
  have hsub : z • H ⊆ A ∩ B := coset_subset_of_periodic hper hz
  constructor
  · rw [Finset.inter_eq_right.2 (hsub.trans Finset.inter_subset_left), Finset.card_smul_finset]
  · rw [Finset.inter_eq_right.2 (hsub.trans Finset.inter_subset_right), Finset.card_smul_finset]

omit [Fintype G] in
/-- **CASE 4.2, step 3d.**  When every mixed pair of cosets is large, every coset pair is. -/
theorem case42_coset_card {A B H : Finset G} {t : ℕ}
    (hper : (A ∩ B) * H = A ∩ B) (hHt : t ≤ H.card)
    (hboth : ∀ a ∈ A, a ∉ B → ∀ b ∈ B, b ∉ A →
        H.card + t ≤ (A ∩ (a • H)).card + (B ∩ (b • H)).card)
    (hA1ne : ∃ a ∈ A, a ∉ B) (hB1ne : ∃ b ∈ B, b ∉ A)
    {a b : G} (ha : a ∈ A) (hb : b ∈ B) :
    H.card + t ≤ (A ∩ (a • H)).card + (B ∩ (b • H)).card := by
  classical
  obtain ⟨a₁, ha₁, ha₁B⟩ := hA1ne
  obtain ⟨b₁, hb₁, hb₁A⟩ := hB1ne
  have hAle : ∀ z : G, (A ∩ (z • H)).card ≤ H.card := by
    intro z
    calc (A ∩ (z • H)).card ≤ (z • H).card := Finset.card_le_card Finset.inter_subset_right
      _ = H.card := Finset.card_smul_finset _ _
  have hBle : ∀ z : G, (B ∩ (z • H)).card ≤ H.card := by
    intro z
    calc (B ∩ (z • H)).card ≤ (z • H).card := Finset.card_le_card Finset.inter_subset_right
      _ = H.card := Finset.card_smul_finset _ _
  have hAt : ∀ z ∈ A, z ∉ B → t ≤ (A ∩ (z • H)).card := by
    intro z hz hzB
    have := hboth z hz hzB b₁ hb₁ hb₁A
    have := hBle b₁
    omega
  have hBt : ∀ z ∈ B, z ∉ A → t ≤ (B ∩ (z • H)).card := by
    intro z hz hzA
    have := hboth a₁ ha₁ ha₁B z hz hzA
    have := hAle a₁
    omega
  by_cases haB : a ∈ B
  · have hfa := (card_inter_coset_of_mem_periodic hper (Finset.mem_inter.2 ⟨ha, haB⟩)).1
    by_cases hbA : b ∈ A
    · have hfb := (card_inter_coset_of_mem_periodic hper (Finset.mem_inter.2 ⟨hbA, hb⟩)).2
      omega
    · have := hBt b hb hbA
      omega
  · have hat := hAt a ha haB
    by_cases hbA : b ∈ A
    · have hfb := (card_inter_coset_of_mem_periodic hper (Finset.mem_inter.2 ⟨hbA, hb⟩)).2
      omega
    · exact hboth a ha haB b hb hbA

/-- **CASE 4.2, step 3d, conclusion.**  Under those card conditions every product is
`t`-representable. -/
theorem case42_repSet_eq {A B H : Finset G} (hH : IsSubgroupFinset H) {t : ℕ} (ht : 1 ≤ t)
    (hper : (A ∩ B) * H = A ∩ B) (hHt : t ≤ H.card)
    (hboth : ∀ a ∈ A, a ∉ B → ∀ b ∈ B, b ∉ A →
        H.card + t ≤ (A ∩ (a • H)).card + (B ∩ (b • H)).card)
    (hA1ne : ∃ a ∈ A, a ∉ B) (hB1ne : ∃ b ∈ B, b ∉ A) :
    repSet A B t = A * B := by
  refine Subset.antisymm (repSet_subset_mul A B ht) (fun c hc => ?_)
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_mul.1 hc
  exact mem_repSet.2 (t_le_rep_of_coset hH (case42_coset_card hper hHt hboth hA1ne hB1ne ha hb))

omit [Fintype G] in
/-- **CASE 4.2, the hole count.**  Two cosets meeting only one of `A`, `B` contribute their
complements to the holes of `A ∪ B`. -/
theorem case42_holes_ge {A B H : Finset G} (hH : IsSubgroupFinset H)
    {a b : G} (ha : a ∈ A) (hb : b ∈ B)
    (haB : ∀ z ∈ B, z ∉ a • H) (hbA : ∀ z ∈ A, z ∉ b • H) :
    2 * H.card ≤ (A ∩ (a • H)).card + (B ∩ (b • H)).card
      + (((A ∪ B) * H) \ (A ∪ B)).card := by
  classical
  have hne : a • H ≠ b • H := by
    intro hcon
    exact haB b hb (by rw [hcon]; exact hH.mem_smul_self b)
  have hdisj : Disjoint ((a • H) \ (A ∪ B)) ((b • H) \ (A ∪ B)) :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset (hH.smul_coset_disjoint hne))
  have hsub : ((a • H) \ (A ∪ B)) ∪ ((b • H) \ (A ∪ B)) ⊆ ((A ∪ B) * H) \ (A ∪ B) := by
    intro z hz
    rcases Finset.mem_union.1 hz with hz | hz <;> rw [Finset.mem_sdiff] at hz ⊢
    · exact ⟨hH.smul_subset_mul (hH.subset_mul (A ∪ B) (Finset.mem_union_left _ ha)) hz.1, hz.2⟩
    · exact ⟨hH.smul_subset_mul (hH.subset_mul (A ∪ B) (Finset.mem_union_right _ hb)) hz.1, hz.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  have hA : ((a • H) ∩ (A ∪ B)).card + ((a • H) \ (A ∪ B)).card = H.card := by
    rw [Finset.card_inter_add_card_sdiff, Finset.card_smul_finset]
  have hB : ((b • H) ∩ (A ∪ B)).card + ((b • H) \ (A ∪ B)).card = H.card := by
    rw [Finset.card_inter_add_card_sdiff, Finset.card_smul_finset]
  have hAeq : (a • H) ∩ (A ∪ B) = A ∩ (a • H) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hz, hzA | hzB⟩
      · exact ⟨hzA, hz⟩
      · exact absurd hz (haB z hzB)
    · rintro ⟨hzA, hz⟩
      exact ⟨hz, Or.inl hzA⟩
  have hBeq : (b • H) ∩ (A ∪ B) = B ∩ (b • H) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hz, hzA | hzB⟩
      · exact absurd hz (hbA z hzA)
      · exact ⟨hzB, hz⟩
    · rintro ⟨hzB, hz⟩
      exact ⟨hz, Or.inr hzB⟩
  rw [hAeq] at hA
  rw [hBeq] at hB
  omega

/-- **CASE 4.2, step 3.**  If some coset of `H` meets `B` but not `A`, then either the conclusion
of Grynkiewicz's theorem already holds or the gap `#H − ρ ≥ t + 1` fails. -/
theorem case42_step3 {A B : Finset G} {t : ℕ} (ht : 1 ≤ t) (hBA : B.card ≤ A.card)
    (hper : (A ∩ B) * mulStab ((A ∪ B) * (A ∩ B)) = A ∩ B)
    (hmax : ∀ z : G, (dysonSmall A B z).Nonempty → (dysonSmall A B z).card < B.card →
        (dysonSmall A B z).card ≤ (dysonSmall A B 1).card)
    (hgap : holes (mulStab ((A ∪ B) * (A ∩ B))) (A ∪ B) (A ∩ B) + t + 1
        ≤ (mulStab ((A ∪ B) * (A ∩ B))).card)
    (hB1 : ∃ b ∈ B, ∀ z ∈ A, z ∉ b • mulStab ((A ∪ B) * (A ∩ B))) :
    PollardConclusion A B t := by
  classical
  set H := mulStab ((A ∪ B) * (A ∩ B)) with hHdef
  have hH : IsSubgroupFinset H := isSubgroupFinset_mulStab _
  obtain ⟨b₁, hb₁, hb₁A⟩ := hB1
  have hb₁B : b₁ ∉ A ∩ B := fun h => hb₁A b₁ (Finset.mem_inter.1 h).1 (hH.mem_smul_self b₁)
  have hperAB : (A ∩ B) * H = A ∩ B := hper
  have hnomix : ∀ a ∈ A, a ∉ B → ∀ z ∈ B, z ∉ a • H := by
    intro a ha haB z hz hzc
    exact case42_no_mixed_coset hH hperAB hmax hb₁ hb₁A ha haB hz hzc
  have hB0 : ∀ b ∈ B, b ∉ A → ∀ z ∈ A, z ∉ b • H := by
    intro b hb hbA z hz hzc
    by_cases hzB : z ∈ B
    · have hsub : z • H ⊆ A ∩ B :=
        coset_subset_of_periodic hperAB (Finset.mem_inter.2 ⟨hz, hzB⟩)
      have hzb : z • H = b • H := hH.smul_eq_smul_of_mem hzc
      have : b ∈ A ∩ B := hsub (by rw [hzb]; exact hH.mem_smul_self b)
      exact hbA (Finset.mem_inter.1 this).1
    · have hbz : b ∉ z • H := hnomix z hz hzB b hb
      exact hbz (by rw [hH.smul_eq_smul_of_mem hzc]; exact hH.mem_smul_self b)
  have hcardlt : (A ∩ B).card + 1 ≤ B.card := by
    have hsub : insert b₁ (A ∩ B) ⊆ B := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hb₁
      · exact (Finset.mem_inter.1 hz).2
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hb₁B] at this
    omega
  have hA1ne : ∃ a ∈ A, a ∉ B := by
    by_contra hcon
    push Not at hcon
    have hsub : A ⊆ A ∩ B := fun z hz => Finset.mem_inter.2 ⟨hz, hcon z hz⟩
    have := Finset.card_le_card hsub
    omega
  have hB1ne : ∃ b ∈ B, b ∉ A := ⟨b₁, hb₁, fun h => hb₁A b₁ h (hH.mem_smul_self b₁)⟩
  by_cases hboth : ∀ a ∈ A, a ∉ B → ∀ b ∈ B, b ∉ A →
      H.card + t ≤ (A ∩ (a • H)).card + (B ∩ (b • H)).card
  · have hHt : t ≤ H.card := by
      have : 0 ≤ holes H (A ∪ B) (A ∩ B) := Nat.zero_le _
      omega
    have hrepset : repSet A B t = A * B :=
      case42_repSet_eq hH ht hperAB hHt hboth hA1ne hB1ne
    have hAne : A.Nonempty := by
      obtain ⟨a, ha, _⟩ := hA1ne
      exact ⟨a, ha⟩
    have hBne : B.Nonempty := ⟨b₁, hb₁⟩
    rcases pollard_step1 A B A B t ht Subset.rfl Subset.rfl hAne hBne
      (by rw [defect]; simpa using ht) (by rw [hrepset]) hrepset.symm with h | h
    · exact Or.inr h
    · exact Or.inl (pollardWeak_of_boundTSq ht h)
  · exfalso
    push Not at hboth
    obtain ⟨a, ha, haB, b, hb, hbA, hlt⟩ := hboth
    have hholes := case42_holes_ge hH ha hb (hnomix a ha haB) (hB0 b hb hbA)
    have hzero : (((A ∩ B) * H) \ (A ∩ B)).card = 0 := by
      rw [hperAB, Finset.sdiff_self]
      rfl
    have hrho : holes H (A ∪ B) (A ∩ B)
        = (((A ∪ B) * H) \ (A ∪ B)).card + (((A ∩ B) * H) \ (A ∩ B)).card := rfl
    omega

end GaloisForLFunctions.HTGeometry.AddComb
