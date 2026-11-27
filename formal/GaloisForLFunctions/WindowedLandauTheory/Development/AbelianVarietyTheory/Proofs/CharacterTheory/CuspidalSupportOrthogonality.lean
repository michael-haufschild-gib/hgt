import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CuspidalSplitDoubleCoset
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CuspidalMatchedDoubleCoset

/-! Mackey's formula separates Harish–Chandra products of distinct cuspidal
multisets. A split block cancels, and an aligned cell pairs only matching labels. -/

noncomputable section
open scoped Classical
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

private theorem multiset_eq_sum_get {α : Type*} (L : List α) :
    (L : Multiset α) = ∑ k : Fin L.length, ({L.get k} : Multiset α) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    let f (k : Fin (L.length + 1)) : Multiset α := {(a :: L).get k}
    change ((a :: L : List α) : Multiset α) = ∑ k : Fin (L.length + 1), f k
    rw [Fin.sum_univ_succ f]
    change ((a :: L : List α) : Multiset α) = {a} + ∑ k : Fin L.length, {L.get k}
    rw [← ih]
    rfl

private theorem listParabolicPairing_eq_zero_of_split_fibre
    (L M : List (Pc g)) (hL : degL L = n) (hM : degL M = n) (σ : Equiv.Perm (Fin n))
    [Fintype (doubleCosetOverlap (listParabolicAt L hL) (listParabolicAt M hM) (permutationUnit σ))]
    (hχ : ∀ k : Fin L.length, IsCusp (L.get k).2)
    (i j : Fin n) (hf : listBlockOfAt L hL i = listBlockOfAt L hL j)
    (hr : permutedListBlockOf M hM σ i ≠ permutedListBlockOf M hM σ j) :
    doubleCosetPairing (listParabolicAt L hL) (listParabolicAt M hM)
      (listParabolicCharacterAt L hL) (listParabolicCharacterAt M hM) (permutationUnit σ) = 0 := by
  let k := listBlockOfAt L hL i
  obtain ⟨a, ha⟩ : ∃ a : Fin (L.get k).1, listBlockEmbeddingAt L hL k a = i :=
    exists_listBlockCoordinateAt L hL i
  obtain ⟨b, hb⟩ : ∃ b : Fin (L.get k).1, listBlockEmbeddingAt L hL k b = j :=
    exists_listBlockCoordinateAt_of_eq L hL hf.symm
  have hne : permutedListBlockOf M hM σ (listBlockEmbeddingAt L hL k a) ≠
      permutedListBlockOf M hM σ (listBlockEmbeddingAt L hL k b) := by
    rwa [ha, hb]
  rcases lt_or_gt_of_ne hne with h | h
  · exact listParabolicPairing_eq_zero_of_split L M hL hM σ k (hχ k) a b h
  · exact listParabolicPairing_eq_zero_of_split L M hL hM σ k (hχ k) b a h

private theorem permutationUnit_inv (σ : Equiv.Perm (Fin n)) :
    (permutationUnit (g := g) σ)⁻¹ = permutationUnit σ.symm := by
  apply Units.ext
  change signedMonomialMatrix σ.symm (fun _ => (1 : (ZMod g)ˣ)⁻¹) =
    signedMonomialMatrix σ.symm (fun _ => (1 : (ZMod g)ˣ))
  simp only [inv_one]

/-- A cell with nonzero pairing matches both block partitions and all cuspidal labels. -/
theorem aligned_labels_of_listParabolicPairing_ne_zero
    (L M : List (Pc g)) (hL : degL L = n) (hM : degL M = n) (σ : Equiv.Perm (Fin n))
    (hχ : ∀ k : Fin L.length, IsCusp (L.get k).2) (hη : ∀ k : Fin M.length, IsCusp (M.get k).2)
    (hn : doubleCosetPairing (listParabolicAt L hL) (listParabolicAt M hM)
      (listParabolicCharacterAt L hL) (listParabolicCharacterAt M hM) (permutationUnit σ) ≠ 0) :
    ∃ e : Fin L.length ≃ Fin M.length,
      (∀ i, e (listBlockOfAt L hL i) = permutedListBlockOf M hM σ i) ∧
      ∀ k, L.get k = M.get (e k) := by
  let f := listBlockOfAt L hL
  let r := permutedListBlockOf M hM σ
  let w : Gn g n := permutationUnit σ
  let P := listParabolicAt L hL
  let Q := listParabolicAt M hM
  letI : Fintype (doubleCosetOverlap P Q w) := Fintype.ofFinite _
  have hf (i j : Fin n) (hij : f i = f j) : r i = r j := by
    by_contra hne
    exact hn (listParabolicPairing_eq_zero_of_split_fibre L M hL hM σ hχ i j hij hne)
  have hr (i j : Fin n) (hij : r i = r j) : f i = f j := by
    by_contra hne
    apply hn
    letI : Fintype (doubleCosetOverlap Q P w⁻¹) := Fintype.ofFinite _
    letI : Fintype (doubleCosetOverlap Q P (permutationUnit σ.symm)) := Fintype.ofFinite _
    rw [doubleCosetPairing_swap_inv P Q w, permutationUnit_inv σ]
    apply listParabolicPairing_eq_zero_of_split_fibre M L hM hL σ.symm hη (σ.symm i) (σ.symm j) hij
    change f (σ (σ.symm i)) ≠ f (σ (σ.symm j))
    simpa only [σ.apply_symm_apply] using hne
  obtain ⟨e, he⟩ := exists_listBlockEquiv L M hL hM σ
    (fun k => (hχ k).1) (fun k => (hη k).1) hf hr
  refine ⟨e, he, fun k => ?_⟩
  by_contra hk
  exact hn (listParabolicPairing_eq_zero_of_matched_ne L M hL hM σ e he
    (fun i => (hχ i).2.1) (fun j => (hη j).2.1) k hk)

private theorem listParabolicPairing_eq_zero_of_multiset_ne
    (L M : List (Pc g)) (hL : degL L = n) (hM : degL M = n) (σ : Equiv.Perm (Fin n))
    (hχ : ∀ k : Fin L.length, IsCusp (L.get k).2) (hη : ∀ k : Fin M.length, IsCusp (M.get k).2)
    (hne : (L : Multiset (Pc g)) ≠ (M : Multiset (Pc g))) :
    doubleCosetPairing (listParabolicAt L hL) (listParabolicAt M hM)
      (listParabolicCharacterAt L hL) (listParabolicCharacterAt M hM) (permutationUnit σ) = 0 := by
  by_contra hn
  obtain ⟨e, _, he⟩ := aligned_labels_of_listParabolicPairing_ne_zero L M hL hM σ hχ hη hn
  apply hne
  calc
    (L : Multiset (Pc g)) = ∑ k : Fin L.length, {L.get k} := multiset_eq_sum_get L
    _ = ∑ k : Fin L.length, {M.get (e k)} := Finset.sum_congr rfl fun k _ =>
      congrArg (fun x : Pc g => ({x} : Multiset (Pc g))) (he k)
    _ = ∑ k : Fin M.length, {M.get k} := Equiv.sum_comp e (fun k => {M.get k})
    _ = (M : Multiset (Pc g)) := (multiset_eq_sum_get M).symm

theorem isChar_of_cuspidal {a : ℕ} {χ : Gn g a → ℂ} (h : IsCusp χ) : IsChar χ := by
  obtain ⟨V, _, hV⟩ := h.2.1
  exact ⟨V, hV⟩

private theorem isClass_of_genuine {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  exact fun x y => (hV (y * x * y⁻¹)).symm.trans ((V.char_conj x y).trans (hV x))

/-- The pairing of iterated Harish–Chandra products is the sum of the normalized flag overlaps. -/
theorem characterPairing_hcL_eq_sum_doubleCosets
    (L M : List (Pc g)) (hL : degL L = n) (hM : degL M = n)
    (hχ : ∀ p ∈ L, IsChar p.2) (hη : ∀ p ∈ M, IsChar p.2) :
    let P := listParabolicAt L hL
    let Q := listParabolicAt M hM
    letI := mixedDoubleCosetFintype P Q
    characterPairing (Gn g n) (hcL L n) (hcL M n) =
      ∑ q : DoubleCoset.Quotient (P : Set (Gn g n)) Q,
        doubleCosetPairing P Q (listParabolicCharacterAt L hL) (listParabolicCharacterAt M hM) q.out := by
  let P := listParabolicAt L hL
  let Q := listParabolicAt M hM
  let α := listParabolicCharacterAt L hL
  let β := listParabolicCharacterAt M hM
  letI := mixedDoubleCosetFintype P Q
  change characterPairing (Gn g n) (hcL L n) (hcL M n) =
    ∑ q : DoubleCoset.Quotient (P : Set (Gn g n)) Q, doubleCosetPairing P Q α β q.out
  obtain ⟨V, hV⟩ := isChar_listParabolicCharacterAt L hL hχ
  obtain ⟨W, hW⟩ := isChar_listParabolicCharacterAt M hM hη
  rw [hcL_eq_inducedFunction_listParabolicAt L hL (fun p hp => isClass_of_genuine (hχ p hp)),
    hcL_eq_inducedFunction_listParabolicAt M hM (fun p hp => isClass_of_genuine (hη p hp))]
  have hm := characterPairing_induced_doubleCosets P Q V.ρ W.ρ
  rwa [show Representation.character V.ρ = α from funext hV,
    show Representation.character W.ρ = β from funext hW] at hm

/-- Harish–Chandra products with unequal cuspidal multisets are orthogonal. -/
theorem characterPairing_hcL_eq_zero_of_multiset_ne
    (L M : List (Pc g)) (hL : degL L = n) (hM : degL M = n)
    (hχ : ∀ p ∈ L, IsCusp p.2) (hη : ∀ p ∈ M, IsCusp p.2)
    (hne : (L : Multiset (Pc g)) ≠ (M : Multiset (Pc g))) :
    characterPairing (Gn g n) (hcL L n) (hcL M n) = 0 := by
  let P := listParabolicAt L hL
  let Q := listParabolicAt M hM
  let α := listParabolicCharacterAt L hL
  let β := listParabolicCharacterAt M hM
  have hLχ (p) (hp : p ∈ L) : IsChar p.2 := isChar_of_cuspidal (hχ p hp)
  have hMη (p) (hp : p ∈ M) : IsChar p.2 := isChar_of_cuspidal (hη p hp)
  rw [characterPairing_hcL_eq_sum_doubleCosets L M hL hM hLχ hMη]
  refine Finset.sum_eq_zero fun q _ => ?_
  obtain ⟨σ, hσ⟩ := exists_listParabolic_permutation_rep L M hL hM q.out
  have ha : IsClass α := isClass_of_genuine (isChar_listParabolicCharacterAt L hL hLχ)
  have hb : IsClass β := isClass_of_genuine (isChar_listParabolicCharacterAt M hM hMη)
  rw [← doubleCosetPairing_eq_of_mk_eq P Q α β ha hb hσ]
  exact listParabolicPairing_eq_zero_of_multiset_ne L M hL hM σ
    (fun k => hχ _ (List.get_mem _ _)) (fun k => hη _ (List.get_mem _ _)) hne

end GlobalTheory.GLq
