import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutWhittakerInduction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicHarishChandra
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerClassFunctions
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CuspidalBlockAllocation
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CuspidalSupportOrthogonality
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.SplitBlockOverlap
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.TwoBlockListParabolic
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.HarishChandraSubsetBound

/-! Each nonzero Mackey contribution to the Whittaker multiplicity of a
derivative allocates whole cuspidal blocks to its two retained flags. -/

noncomputable section
open GaloisForLFunctions
open scoped Classical

namespace GlobalTheory.GLq

variable {g a b m : ℕ} [Fact g.Prime]

private theorem class_of_genuine {G : Type} [Group G] {χ : G → ℂ} (hχ : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := hχ
  exact fun x y => (hV _).symm.trans ((V.char_conj x y).trans (hV x))

private theorem wh_hcL_eq_one (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (L : List (Pc g))
    (hL : ∀ p ∈ L, IsCusp p.2 ∧ wh ψ p.2 = 1) :
    wh ψ (hcL L (degL L)) = 1 := by
  induction L with
  | nil => exact wh_rank_zero ψ (fun _ => 1)
  | cons p L ih =>
    have hp := hL p List.mem_cons_self
    have h := fun q hq => hL q (List.mem_cons_of_mem p hq)
    change wh ψ (hc p.1 (degL L) p.2 (hcL L (degL L)) (p.1 + degL L)) = 1
    rw [wh_hc_mul_of_isClass ψ hψ (class_of_genuine (isChar_of_cuspidal hp.1))
      (class_of_genuine (isChar_hcL L fun q hq => isChar_of_cuspidal (h q hq).1)), hp.2, ih h, one_mul]

private theorem flagPairing_gg_eq_one (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1)
    (L : List (Pc g)) (hL : degL L = m) (h : ∀ p ∈ L, IsCusp p.2 ∧ wh ψ p.2 = 1) :
    characterPairing (listParabolicAt L hL) (listParabolicCharacterAt L hL)
      (fun u => gg ψ m u.val) = 1 := by
  let P := listParabolicAt L hL
  let φ := listParabolicCharacterAt L hL
  have hc (p : Pc g) (hp : p ∈ L) : IsChar p.2 := isChar_of_cuspidal (h p hp).1
  obtain ⟨V, hV⟩ := isChar_listParabolicCharacterAt L hL hc
  obtain ⟨W, hW⟩ := isChar_gg ψ m
  have e₁ : Representation.character V.ρ = φ := funext hV
  have e₂ : Representation.character W.ρ = gg ψ m := funext hW
  have e₃ : Representation.character (W.ρ.comp P.subtype) = fun u : P => gg ψ m u.val :=
    funext fun u => hW u.val
  have hFR := characterPairing_induced_restricted P.subtype V.ρ W.ρ
  rw [induced_character_eq_inducedFunction P, e₁, e₂, e₃,
    ← hcL_eq_inducedFunction_listParabolicAt L hL (fun p hp => class_of_genuine (hc p hp))] at hFR
  rw [← hFR, characterPairing_comm, characterPairing, Nat.card_eq_fintype_card]
  change ip (hcL L m) (gg ψ m) = 1
  subst m
  rw [ip_gg ψ _ _ (class_of_genuine (isChar_hcL L hc)), wh_hcL_eq_one ψ hψ L h]

omit [Fact g.Prime] in
private theorem selectBlocks_mem {L : List (Pc g)} {S : Finset (Fin L.length)}
    {p : Pc g} (hp : p ∈ selectBlocks L S) : p ∈ L := by
  unfold selectBlocks at hp
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp
  exact List.get_mem _ _

omit [Fact g.Prime] in
private theorem permutedListBlockOf_split_val (L : List (Pc g)) (hL : degL L = a + b)
    (S : Finset (Fin L.length)) (hA : degL (selectBlocks L S) = a)
    (hB : degL (selectBlocks L Sᶜ) = b) (α : Gn g a → ℂ) (β : Gn g b → ℂ)
    (i : Fin (a + b)) :
    (permutedListBlockOf (blockPair α β) (degL_blockPair α β)
      (splitBlockPermutation L hL S hA hB) i).val =
        if listBlockOfAt L hL i ∈ S then 0 else 1 := by
  let σ := splitBlockPermutation L hL S hA hB
  obtain ⟨j, rfl⟩ := σ.surjective i
  rw [permutedListBlockOf, σ.symm_apply_apply, listBlockOfAt_blockPair_val]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · have h := (mem_range_selectBlockCoordinate L hL S hA _).mp ⟨i, rfl⟩
    change (if (i : ℕ) < a then 0 else 1) =
      if listBlockOfAt L hL (σ (Fin.castAdd b i)) ∈ S then 0 else 1
    rw [splitBlockPermutation_castAdd, if_pos i.isLt, if_pos h]
  · have h := Finset.mem_compl.mp
      ((mem_range_selectBlockCoordinate L hL Sᶜ hB _).mp ⟨i, rfl⟩)
    change (if a + (i : ℕ) < a then 0 else 1) =
      if listBlockOfAt L hL (σ (Fin.natAdd a i)) ∈ S then 0 else 1
    rw [splitBlockPermutation_natAdd, if_neg (not_lt_of_ge (Nat.le_add_right a i.val)), if_neg h]

private theorem nonzero_cuspidalDerivative_cell_eq_one (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1)
    (L : List (Pc g)) (hL : degL L = a + b) (h : ∀ p ∈ L, IsCusp p.2 ∧ wh ψ p.2 = 1)
    (x : Gn g (a + b)) :
    let M := blockPair (gg ψ a) (gg ψ b)
    let hM := degL_blockPair (gg ψ a) (gg ψ b)
    let P := listParabolicAt L hL
    let Q := listParabolicAt M hM
    let v := doubleCosetPairing P Q (listParabolicCharacterAt L hL) (listParabolicCharacterAt M hM) x
    v ≠ 0 → v = 1 := by
  let M := blockPair (gg ψ a) (gg ψ b)
  let hM := degL_blockPair (gg ψ a) (gg ψ b)
  let P := listParabolicAt L hL
  let Q := listParabolicAt M hM
  let α := listParabolicCharacterAt L hL
  let β := listParabolicCharacterAt M hM
  have hα : IsClass α := class_of_genuine (isChar_listParabolicCharacterAt L hL
    fun p hp => isChar_of_cuspidal (h p hp).1)
  have hβ : IsClass β := class_of_genuine (isChar_listParabolicCharacterAt M hM fun p hp => by
    have he : p = (⟨a, gg ψ a⟩ : Pc g) ∨ p = (⟨b, gg ψ b⟩ : Pc g) := by
      simpa [M, blockPair] using hp
    rcases he with rfl | rfl
    · exact isChar_gg ψ a
    · exact isChar_gg ψ b)
  obtain ⟨σ, hσ⟩ := exists_listParabolic_permutation_rep L M hL hM x
  change doubleCosetPairing P Q α β x ≠ 0 → doubleCosetPairing P Q α β x = 1
  rw [doubleCosetPairing_eq_of_mk_eq P Q α β hα hβ hσ.symm]
  intro hn
  letI : Fintype (doubleCosetOverlap P Q (permutationUnit σ)) := Fintype.ofFinite _
  let t (k : Fin L.length) : Fin 2 := permutedListBlockOf M hM σ
    (listBlockEmbeddingAt L hL k ⟨0, (h (L.get k) (List.get_mem L k)).1.1⟩)
  have ht (k : Fin L.length) (i : Fin (L.get k).1) :
      permutedListBlockOf M hM σ (listBlockEmbeddingAt L hL k i) = t k :=
    permutedBlockOf_eq_of_pairing_ne_zero L M hL hM σ k (h _ (List.get_mem L k)).1 hn i _
  let S := Finset.univ.filter fun k => t k = 0
  have h1 : Sᶜ = Finset.univ.filter fun k => t k = 1 := by
    ext k
    simp only [S, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
    have hk := (t k).isLt
    simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one]
    omega
  have hA : degL (selectBlocks L S) = a := by
    rw [degL_selectBlocks]
    exact sum_ranks_of_block_allocation L M hL hM σ t ht (0 : Fin 2)
  have hB : degL (selectBlocks L Sᶜ) = b := by
    rw [degL_selectBlocks, h1]
    exact sum_ranks_of_block_allocation L M hL hM σ t ht (1 : Fin 2)
  let τ := splitBlockPermutation L hL S hA hB
  have he : DoubleCoset.mk P Q (permutationUnit σ) = DoubleCoset.mk P Q (permutationUnit τ) := by
    apply listParabolic_coset_eq_of_targetBlocks_eq L M hL hM
    intro i
    have hi : permutedListBlockOf M hM σ i = t (listBlockOfAt L hL i) := by
      obtain ⟨j, hj⟩ := exists_listBlockCoordinateAt L hL i
      exact (congrArg (permutedListBlockOf M hM σ) hj).symm.trans (ht _ j)
    apply Fin.ext
    rw [hi, permutedListBlockOf_split_val L hL S hA hB (gg ψ a) (gg ψ b) i]
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    have hz := (t (listBlockOfAt L hL i)).isLt
    split_ifs with hzero
    · exact congrArg Fin.val hzero
    · have ht' : (t (listBlockOfAt L hL i)).val ≠ 0 := fun e => hzero (Fin.ext e)
      omega
  rw [doubleCosetPairing_eq_of_mk_eq P Q α β hα hβ he,
    doubleCosetPairing_blockPair (gg ψ a) (gg ψ b),
    doubleCosetPairing_splitBlockPermutation L hL S hA hB,
    flagPairing_gg_eq_one ψ hψ _ hA (fun p hp => h p (selectBlocks_mem hp)),
    flagPairing_gg_eq_one ψ hψ _ hB (fun p hp => h p (selectBlocks_mem hp)), one_mul]

/-- The Whittaker multiplicity of a derivative is bounded by the number
of cuspidal block subsets of the retained rank. -/
theorem wh_der_hcL_re_le_subsetRankCount (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1)
    (L : List (Pc g)) (hL : degL L = a + b) (h : ∀ p ∈ L, IsCusp p.2 ∧ wh ψ p.2 = 1) :
    (wh ψ (der ψ a (hcL L (a + b)))).re ≤ subsetRankCount (fun k : Fin L.length => (L.get k).1) a := by
  let M := blockPair (gg ψ a) (gg ψ b)
  let hM := degL_blockPair (gg ψ a) (gg ψ b)
  let P := listParabolicAt L hL
  let Q := listParabolicAt M hM
  let D := DoubleCoset.Quotient (P : Set (Gn g (a + b))) Q
  letI : Fintype D := mixedDoubleCosetFintype P Q
  let c (d : D) := doubleCosetPairing P Q (listParabolicCharacterAt L hL)
    (listParabolicCharacterAt M hM) d.out
  have hLchar (p : Pc g) (hp : p ∈ L) : IsChar p.2 := isChar_of_cuspidal (h p hp).1
  have hchars : ∀ p ∈ M, IsChar p.2 := by
    intro p hp
    have he : p = (⟨a, gg ψ a⟩ : Pc g) ∨ p = (⟨b, gg ψ b⟩ : Pc g) := by
      simpa [M, blockPair] using hp
    rcases he with rfl | rfl
    · exact isChar_gg ψ a
    · exact isChar_gg ψ b
  have hgg : hcL M (a + b) = hc a b (gg ψ a) (gg ψ b) (a + b) := by
    change hc a b (gg ψ a) (hc b 0 (gg ψ b) (fun _ => 1) b) (a + b) = _
    rw [← gg_zero ψ, hc_gg_zero ψ _ (class_of_genuine (isChar_gg ψ b))]
  have hsum : wh ψ (der ψ a (hcL L (a + b))) = ∑ d : D, c d := by
    rw [wh_der_eq_pairing_hc_gg_gg ψ _ (hL ▸ isChar_hcL L hLchar), ← hgg]
    exact characterPairing_hcL_eq_sum_doubleCosets L M hL hM hLchar hchars
  have he (d : D) : c d = if c d ≠ 0 then (1 : ℂ) else 0 := by
    split_ifs with hn
    · exact nonzero_cuspidalDerivative_cell_eq_one ψ hψ L hL h d.out hn
    · exact not_ne_iff.mp hn
  have hcount : Fintype.card {d : D // c d ≠ 0} ≤
      subsetRankCount (fun k : Fin L.length => (L.get k).1) a := by
    have hc' := card_nonzero_listParabolicPairing_twoBlocks_le L
      (⟨a, gg ψ a⟩ : Pc g) (⟨b, gg ψ b⟩ : Pc g) hL
      (fun p hp => (h p hp).1) (isChar_gg ψ a) (isChar_gg ψ b)
    rw [subsetRankCount, ← Fintype.card_subtype]
    exact hc'
  rw [hsum, Finset.sum_congr rfl (fun d _ => he d), Finset.sum_boole, Complex.natCast_re,
    ← Fintype.card_subtype]
  exact_mod_cast hcount

end GlobalTheory.GLq
