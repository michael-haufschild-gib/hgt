import GaloisForLFunctions.HTGeometry.OccupationSubsetPrimitivity
import GaloisForLFunctions.HTGeometry.TranspositionTransitive

/-!
# Johnson-edge generation on critical occupation states

Balanced occupation-subset action has complement-pair blocks, so earlier primitivity argument
deliberately excluded `m = n`. This module removes that restriction. Root permutations act
transitively on ordered adjacent pairs in Johnson graph. Conjugating one adjacent state transposition
therefore supplies every Johnson-edge transposition, and those transpositions generate full symmetric
group because Johnson graph is connected.

Result is uniform in all positive occupation ranks and replaces balanced-case primitivity with
stronger, exact root-action-plus-adjacent-swap criterion needed by geometric monodromy.
-/

namespace GaloisForLFunctions.HTGeometry

open Equiv MulAction Set Finset
open scoped Pointwise

variable {α : Type*} [DecidableEq α]

/-- A root permutation fixing `S` and carrying one Johnson neighbor of `S` to another. -/
lemma exists_perm_fix_smul_finset_of_adjacent
    {k : ℕ} (hk : 0 < k) (S T U : Finset α)
    (hS : S.card = k) (hT : T.card = k) (hU : U.card = k)
    (hST : (S ∩ T).card = k - 1)
    (hSU : (S ∩ U).card = k - 1) :
    ∃ σ : Equiv.Perm α, σ • S = S ∧ σ • T = U := by
  have hST₁ : (S \ T).card = 1 := by
    have h := Finset.card_sdiff_add_card_inter S T
    rw [hS, hST] at h
    omega
  have hTS₁ : (T \ S).card = 1 := by
    have h := Finset.card_sdiff_add_card_inter T S
    rw [hT, Finset.inter_comm, hST] at h
    omega
  have hSU₁ : (S \ U).card = 1 := by
    have h := Finset.card_sdiff_add_card_inter S U
    rw [hS, hSU] at h
    omega
  have hUS₁ : (U \ S).card = 1 := by
    have h := Finset.card_sdiff_add_card_inter U S
    rw [hU, Finset.inter_comm, hSU] at h
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hST₁
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hTS₁
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hSU₁
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hUS₁
  have haS : a ∈ S := by
    have : a ∈ S \ T := by rw [ha]; simp
    exact Finset.mem_sdiff.mp this |>.1
  have haT : a ∉ T := by
    have : a ∈ S \ T := by rw [ha]; simp
    exact Finset.mem_sdiff.mp this |>.2
  have hbT : b ∈ T := by
    have : b ∈ T \ S := by rw [hb]; simp
    exact Finset.mem_sdiff.mp this |>.1
  have hbS : b ∉ S := by
    have : b ∈ T \ S := by rw [hb]; simp
    exact Finset.mem_sdiff.mp this |>.2
  have hcS : c ∈ S := by
    have : c ∈ S \ U := by rw [hc]; simp
    exact Finset.mem_sdiff.mp this |>.1
  have hcU : c ∉ U := by
    have : c ∈ S \ U := by rw [hc]; simp
    exact Finset.mem_sdiff.mp this |>.2
  have hdU : d ∈ U := by
    have : d ∈ U \ S := by rw [hd]; simp
    exact Finset.mem_sdiff.mp this |>.1
  have hdS : d ∉ S := by
    have : d ∈ U \ S := by rw [hd]; simp
    exact Finset.mem_sdiff.mp this |>.2
  have hTform : T = insert b (S.erase a) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_erase]
    constructor
    · intro hxT
      by_cases hxS : x ∈ S
      · exact Or.inr ⟨fun hxa ↦ haT (hxa ▸ hxT), hxS⟩
      · left
        have : x ∈ T \ S := Finset.mem_sdiff.mpr ⟨hxT, hxS⟩
        rw [hb] at this
        exact Finset.mem_singleton.mp this
    · rintro (rfl | ⟨hxa, hxS⟩)
      · exact hbT
      · by_contra hxT
        have : x ∈ S \ T := Finset.mem_sdiff.mpr ⟨hxS, hxT⟩
        rw [ha] at this
        exact hxa (Finset.mem_singleton.mp this)
  have hUform : U = insert d (S.erase c) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_erase]
    constructor
    · intro hxU
      by_cases hxS : x ∈ S
      · exact Or.inr ⟨fun hxc ↦ hcU (hxc ▸ hxU), hxS⟩
      · left
        have : x ∈ U \ S := Finset.mem_sdiff.mpr ⟨hxU, hxS⟩
        rw [hd] at this
        exact Finset.mem_singleton.mp this
    · rintro (rfl | ⟨hxc, hxS⟩)
      · exact hdU
      · by_contra hxU
        have : x ∈ S \ U := Finset.mem_sdiff.mpr ⟨hxS, hxU⟩
        rw [hc] at this
        exact hxc (Finset.mem_singleton.mp this)
  let σ : Equiv.Perm α := Equiv.swap a c * Equiv.swap b d
  refine ⟨σ, ?_, ?_⟩
  · ext x
    simp only [Finset.mem_smul_finset, Equiv.Perm.smul_def, Equiv.Perm.mul_apply, σ]
    constructor
    · rintro ⟨y, hyS, rfl⟩
      simp only [Equiv.swap_apply_def]
      split_ifs <;> grind
    · intro hxS
      refine ⟨σ⁻¹ x, ?_, ?_⟩
      simp only [σ, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
        Equiv.swap_apply_def]
      split_ifs <;> grind
      change σ (σ⁻¹ x) = x
      exact σ.apply_symm_apply x
  · ext x
    simp only [Finset.mem_smul_finset, Equiv.Perm.smul_def, Equiv.Perm.mul_apply, σ]
    constructor
    · rintro ⟨y, hyT, rfl⟩
      rw [hTform] at hyT
      simp only [Equiv.swap_apply_def]
      split_ifs <;> grind
    · intro hxU
      rw [hUform] at hxU
      refine ⟨σ⁻¹ x, ?_, ?_⟩
      simp only [σ, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
        Equiv.swap_apply_def]
      rw [hTform]
      split_ifs <;> grind
      change σ (σ⁻¹ x) = x
      exact σ.apply_symm_apply x

/-- Root permutations are transitive on ordered Johnson edges. -/
lemma exists_perm_smul_finset_pair_of_adjacent
    {k : ℕ} (hk : 0 < k) (S T U V : Finset α)
    (hS : S.card = k) (hT : T.card = k)
    (hU : U.card = k) (hV : V.card = k)
    (hST : (S ∩ T).card = k - 1)
    (hUV : (U ∩ V).card = k - 1) :
    ∃ σ : Equiv.Perm α, σ • S = U ∧ σ • T = V := by
  obtain ⟨σ, hσSmap⟩ := Equiv.Perm.exists_map_finset_eq S U (hS.trans hU.symm)
  have hσS : σ • S = U := by
    simpa only [Finset.smul_finset_def, Finset.map_eq_image,
      Equiv.Perm.smul_def, Equiv.coe_toEmbedding] using hσSmap
  have hUσT : (U ∩ σ • T).card = k - 1 := by
    rw [← hσS, ← Finset.smul_finset_inter, Finset.card_smul_finset]
    exact hST
  obtain ⟨τ, hτU, hτT⟩ := exists_perm_fix_smul_finset_of_adjacent
    hk U (σ • T) V hU (by rw [Finset.card_smul_finset, hT]) hV hUσT hUV
  refine ⟨τ * σ, ?_, ?_⟩
  · rw [mul_smul, hσS, hτU]
  · rw [mul_smul, hτT]

/-- State transpositions along edges of fixed-cardinality Johnson graph. -/
def finsetCardAdjacentSwaps (α : Type*) [DecidableEq α] (k : ℕ) :
    Set (Equiv.Perm {S : Finset α // S.card = k}) :=
  {g | ∃ S T : {S : Finset α // S.card = k},
    (S.1 ∩ T.1).card = k - 1 ∧ g = Equiv.swap S T}

lemma swap_mem_closure_finsetCardAdjacentSwaps
    {k : ℕ} (hk : 0 < k) (S T : {S : Finset α // S.card = k}) :
    Equiv.swap S T ∈ Subgroup.closure (finsetCardAdjacentSwaps α k) := by
  classical
  refine Nat.strong_induction_on
    (p := fun d ↦ ∀ S : {S : Finset α // S.card = k},
      (S.1 \ T.1).card = d →
        Equiv.swap S T ∈ Subgroup.closure (finsetCardAdjacentSwaps α k))
    (S.1 \ T.1).card ?_ S rfl
  intro d ih S hd
  by_cases hST : S = T
  · subst T
    rw [Equiv.swap_self]
    exact (Subgroup.closure (finsetCardAdjacentSwaps α k)).one_mem
  have hnotST : ¬S.1 ⊆ T.1 := by
    intro hsub
    apply hST
    apply Subtype.ext
    exact Finset.eq_of_subset_of_card_le hsub (by rw [S.2, T.2])
  have hnotTS : ¬T.1 ⊆ S.1 := by
    intro hsub
    apply hST
    apply Subtype.ext
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [T.2, S.2])).symm
  obtain ⟨a, ha⟩ := Finset.sdiff_nonempty.mpr hnotST
  obtain ⟨b, hb⟩ := Finset.sdiff_nonempty.mpr hnotTS
  have haS : a ∈ S.1 := Finset.mem_sdiff.mp ha |>.1
  have haT : a ∉ T.1 := Finset.mem_sdiff.mp ha |>.2
  have hbT : b ∈ T.1 := Finset.mem_sdiff.mp hb |>.1
  have hbS : b ∉ S.1 := Finset.mem_sdiff.mp hb |>.2
  let Uval : Finset α := insert b (S.1.erase a)
  have hUcard : Uval.card = k := by
    rw [Finset.card_insert_of_notMem, Finset.card_erase_of_mem haS, S.2]
    · omega
    · exact fun hbErase ↦ hbS (Finset.mem_of_mem_erase hbErase)
  let U : {S : Finset α // S.card = k} := ⟨Uval, hUcard⟩
  have hSUinter : S.1 ∩ U.1 = S.1.erase a := by
    ext x
    simp only [U, Uval, Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    grind
  have hSUadjacent : (S.1 ∩ U.1).card = k - 1 := by
    rw [hSUinter, Finset.card_erase_of_mem haS, S.2]
  have hUTdiff : U.1 \ T.1 = (S.1 \ T.1).erase a := by
    ext x
    simp only [U, Uval, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    grind
  have haDiff : a ∈ S.1 \ T.1 := Finset.mem_sdiff.mpr ⟨haS, haT⟩
  have hlt : (U.1 \ T.1).card < d := by
    rw [hUTdiff]
    exact (Finset.card_erase_lt_of_mem haDiff).trans_eq hd
  have hSU : Equiv.swap S U ∈
      Subgroup.closure (finsetCardAdjacentSwaps α k) := by
    apply Subgroup.subset_closure
    exact ⟨S, U, hSUadjacent, rfl⟩
  have hUT : Equiv.swap U T ∈
      Subgroup.closure (finsetCardAdjacentSwaps α k) :=
    ih _ hlt U rfl
  exact SubmonoidClass.swap_mem_trans
    (Subgroup.closure (finsetCardAdjacentSwaps α k)) hSU hUT

theorem closure_finsetCardAdjacentSwaps_eq_top
    [Fintype α] {k : ℕ} (hk : 0 < k) :
    Subgroup.closure (finsetCardAdjacentSwaps α k) = ⊤ := by
  apply eq_top_of_isSwap_of_transitive
  · rintro g ⟨S, T, hST, rfl⟩
    rw [Equiv.Perm.swap_isSwap_iff]
    intro h
    subst T
    have : k = k - 1 := by simpa [S.2] using hST
    omega
  · intro S T
    exact (swap_mem_closure_isSwap (fun g hg ↦ by
      rcases hg with ⟨U, V, hUV, rfl⟩
      rw [Equiv.Perm.swap_isSwap_iff]
      intro h
      subst V
      have : k = k - 1 := by simpa [U.2] using hUV
      omega)).mp (swap_mem_closure_finsetCardAdjacentSwaps hk S T)

/-- Johnson-edge transpositions on critical occupation states. -/
def criticalOccupationAdjacentSwaps (m n : ℕ) :
    Set (Equiv.Perm (criticalHorizonOccupationStates m n)) :=
  {g | ∃ S T : criticalHorizonOccupationStates m n,
    (S.1 ∩ T.1).card = m - 1 ∧ g = Equiv.swap S T}

lemma swap_mem_closure_criticalOccupationAdjacentSwaps
    {m n : ℕ} (hm : 0 < m)
    (S T : criticalHorizonOccupationStates m n) :
    Equiv.swap S T ∈ Subgroup.closure (criticalOccupationAdjacentSwaps m n) := by
  classical
  refine Nat.strong_induction_on
    (p := fun d ↦ ∀ S : criticalHorizonOccupationStates m n,
      (S.1 \ T.1).card = d →
        Equiv.swap S T ∈ Subgroup.closure (criticalOccupationAdjacentSwaps m n))
    (S.1 \ T.1).card ?_ S rfl
  intro d ih S hd
  by_cases hST : S = T
  · subst T
    rw [Equiv.swap_self]
    exact (Subgroup.closure (criticalOccupationAdjacentSwaps m n)).one_mem
  have hnotST : ¬S.1 ⊆ T.1 := by
    intro hsub
    apply hST
    apply Subtype.ext
    exact Finset.eq_of_subset_of_card_le hsub (by rw [S.2, T.2])
  have hnotTS : ¬T.1 ⊆ S.1 := by
    intro hsub
    apply hST
    apply Subtype.ext
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [T.2, S.2])).symm
  obtain ⟨a, ha⟩ := Finset.sdiff_nonempty.mpr hnotST
  obtain ⟨b, hb⟩ := Finset.sdiff_nonempty.mpr hnotTS
  have haS : a ∈ S.1 := Finset.mem_sdiff.mp ha |>.1
  have haT : a ∉ T.1 := Finset.mem_sdiff.mp ha |>.2
  have hbT : b ∈ T.1 := Finset.mem_sdiff.mp hb |>.1
  have hbS : b ∉ S.1 := Finset.mem_sdiff.mp hb |>.2
  let Uval : Finset (Fin (m + n)) := insert b (S.1.erase a)
  have hUcard : Uval.card = m := by
    rw [Finset.card_insert_of_notMem, Finset.card_erase_of_mem haS, S.2]
    · omega
    · exact fun hbErase ↦ hbS (Finset.mem_of_mem_erase hbErase)
  let U : criticalHorizonOccupationStates m n := ⟨Uval, hUcard⟩
  have hSUinter : S.1 ∩ U.1 = S.1.erase a := by
    ext x
    simp only [U, Uval, Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    grind
  have hSUadjacent : (S.1 ∩ U.1).card = m - 1 := by
    rw [hSUinter, Finset.card_erase_of_mem haS, S.2]
  have hUTdiff : U.1 \ T.1 = (S.1 \ T.1).erase a := by
    ext x
    simp only [U, Uval, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    grind
  have haDiff : a ∈ S.1 \ T.1 := Finset.mem_sdiff.mpr ⟨haS, haT⟩
  have hlt : (U.1 \ T.1).card < d := by
    rw [hUTdiff]
    exact (Finset.card_erase_lt_of_mem haDiff).trans_eq hd
  have hSU : Equiv.swap S U ∈
      Subgroup.closure (criticalOccupationAdjacentSwaps m n) := by
    apply Subgroup.subset_closure
    exact ⟨S, U, hSUadjacent, rfl⟩
  have hUT : Equiv.swap U T ∈
      Subgroup.closure (criticalOccupationAdjacentSwaps m n) :=
    ih _ hlt U rfl
  exact SubmonoidClass.swap_mem_trans
    (Subgroup.closure (criticalOccupationAdjacentSwaps m n)) hSU hUT

theorem closure_criticalOccupationAdjacentSwaps_eq_top
    {m n : ℕ} (hm : 0 < m) :
    Subgroup.closure (criticalOccupationAdjacentSwaps m n) = ⊤ := by
  apply eq_top_of_isSwap_of_transitive
  · rintro g ⟨S, T, hST, rfl⟩
    rw [Equiv.Perm.swap_isSwap_iff]
    intro h
    subst T
    have : m = m - 1 := by simpa [S.2] using hST
    omega
  · intro S T
    exact (swap_mem_closure_isSwap (fun g hg ↦ by
      rcases hg with ⟨U, V, hUV, rfl⟩
      rw [Equiv.Perm.swap_isSwap_iff]
      intro h
      subst V
      have : m = m - 1 := by simpa [U.2] using hUV
      omega)).mp (swap_mem_closure_criticalOccupationAdjacentSwaps hm S T)

/-- Root permutations plus one adjacent state transposition generate full symmetric group. -/
theorem criticalMonodromy_eq_top_of_rootAction_of_adjacentSwap
    {m n : ℕ} (hm : 0 < m)
    (G : Subgroup (Equiv.Perm (criticalHorizonOccupationStates m n)))
    (hroot : ∀ σ, criticalOccupationRootAction m n σ ∈ G)
    (S T : criticalHorizonOccupationStates m n)
    (hST : (S.1 ∩ T.1).card = m - 1)
    (hSwap : Equiv.swap S T ∈ G) :
    G = ⊤ := by
  have hEdges : criticalOccupationAdjacentSwaps m n ⊆ G := by
    rintro g ⟨U, V, hUV, rfl⟩
    obtain ⟨σ, hσS, hσT⟩ := exists_perm_smul_finset_pair_of_adjacent
      hm S.1 T.1 U.1 V.1 S.2 T.2 U.2 V.2 hST hUV
    have hσG : criticalOccupationRootAction m n σ ∈ G := hroot σ
    have hconj : criticalOccupationRootAction m n σ * Equiv.swap S T *
        (criticalOccupationRootAction m n σ)⁻¹ ∈ G :=
      G.mul_mem (G.mul_mem hσG hSwap) (G.inv_mem hσG)
    have hactS : criticalOccupationRootAction m n σ S = U := by
      apply Subtype.ext
      exact hσS
    have hactT : criticalOccupationRootAction m n σ T = V := by
      apply Subtype.ext
      exact hσT
    rw [← hactS, ← hactT, Equiv.swap_apply_apply]
    exact hconj
  have hclosure : Subgroup.closure
      (criticalOccupationAdjacentSwaps m n) ≤ G :=
    (Subgroup.closure_le G).2 hEdges
  rw [closure_criticalOccupationAdjacentSwaps_eq_top hm] at hclosure
  exact top_unique hclosure

end GaloisForLFunctions.HTGeometry


