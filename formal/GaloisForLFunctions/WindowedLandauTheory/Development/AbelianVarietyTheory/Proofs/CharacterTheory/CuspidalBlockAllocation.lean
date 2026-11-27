import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CuspidalSplitDoubleCoset

/-! A nonvanishing cuspidal Mackey cell sends every original block into a
single target block. That assignment determines the cell. -/

noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Classical

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

/-- Two permutation representatives with the same target block for every
coordinate differ by an element of the target parabolic. -/
theorem listParabolic_coset_eq_of_targetBlocks_eq (L M : List (Pc g))
    (hL : degL L = n) (hM : degL M = n) (σ τ : Equiv.Perm (Fin n))
    (h : ∀ i, permutedListBlockOf M hM σ i = permutedListBlockOf M hM τ i) :
    DoubleCoset.mk (listParabolicAt L hL) (listParabolicAt M hM) (permutationUnit σ) =
      DoubleCoset.mk (listParabolicAt L hL) (listParabolicAt M hM) (permutationUnit τ) := by
  let P := listParabolicAt L hL
  let Q := listParabolicAt M hM
  let ρ := τ.trans σ.symm
  have hρ (j : Fin n) : listBlockOfAt M hM (ρ j) = listBlockOfAt M hM j := by
    have he := h (τ j)
    change listBlockOfAt M hM (ρ j) = listBlockOfAt M hM (τ.symm (τ j)) at he
    rwa [τ.symm_apply_apply] at he
  have hQ : permutationUnit ρ ∈ Q := by
    apply (mem_listParabolicAt_iff M hM _).mpr
    intro i j hij
    have hne : i ≠ ρ j := fun e => (ne_of_lt hij) ((congrArg (listBlockOfAt M hM) e).trans (hρ j)).symm
    simp [monomialUnit, signedMonomialMatrix, hne]
  refine (DoubleCoset.eq P Q _ _).mpr ⟨1, P.one_mem, permutationUnit ρ, hQ, ?_⟩
  rw [one_mul]
  apply Units.ext
  change signedMonomialMatrix τ (fun _ => 1) =
    signedMonomialMatrix σ (fun _ => 1) * signedMonomialMatrix ρ (fun _ => 1)
  rw [signedMonomialMatrix_mul]
  have he : ρ.trans σ = τ := Equiv.ext fun i => σ.apply_symm_apply (τ i)
  simp only [he, one_mul]

/-- In a nonzero Mackey cell every coordinate of an original cuspidal
block lies in the same target block. -/
theorem permutedBlockOf_eq_of_pairing_ne_zero (L M : List (Pc g))
    (hL : degL L = n) (hM : degL M = n) (σ : Equiv.Perm (Fin n))
    [Fintype (doubleCosetOverlap (listParabolicAt L hL) (listParabolicAt M hM) (permutationUnit σ))]
    (k : Fin L.length) (hc : IsCusp (L.get k).2)
    (hn : doubleCosetPairing (listParabolicAt L hL) (listParabolicAt M hM)
      (listParabolicCharacterAt L hL) (listParabolicCharacterAt M hM) (permutationUnit σ) ≠ 0)
    (i j : Fin (L.get k).1) :
    permutedListBlockOf M hM σ (listBlockEmbeddingAt L hL k i) =
      permutedListBlockOf M hM σ (listBlockEmbeddingAt L hL k j) := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hn (listParabolicPairing_eq_zero_of_split L M hL hM σ k hc i j h)
  · exact hn (listParabolicPairing_eq_zero_of_split L M hL hM σ k hc j i h)

omit [Fact g.Prime] in
/-- An allocation without splits fills each target block with exactly its rank
in source coordinates. -/
theorem sum_ranks_of_block_allocation (L M : List (Pc g))
    (hL : degL L = n) (hM : degL M = n) (σ : Equiv.Perm (Fin n))
    (t : Fin L.length → Fin M.length)
    (ht : ∀ k (i : Fin (L.get k).1),
      permutedListBlockOf M hM σ (listBlockEmbeddingAt L hL k i) = t k)
    (j : Fin M.length) :
    ∑ k ∈ Finset.univ.filter (fun k => t k = j), (L.get k).1 = (M.get j).1 := by
  let A := Σ k : {k : Fin L.length // t k = j}, Fin (L.get k.val).1
  let source (u : A) := listBlockEmbeddingAt L hL u.1.val u.2
  have hx (u : A) : listBlockOfAt M hM (σ.symm (source u)) = j :=
    (ht u.1.val u.2).trans u.1.property
  let f (u : A) := (exists_listBlockCoordinateAt_of_eq M hM (hx u)).choose
  have hf (u : A) : listBlockEmbeddingAt M hM j (f u) = σ.symm (source u) :=
    (exists_listBlockCoordinateAt_of_eq M hM (hx u)).choose_spec
  have hinj : Function.Injective f := by
    rintro ⟨⟨k, hk⟩, x⟩ ⟨⟨l, hl⟩, y⟩ h
    have hv := congrArg (listBlockEmbeddingAt M hM j) h
    rw [hf, hf] at hv
    have hu := σ.symm.injective hv
    change listBlockEmbeddingAt L hL k x = listBlockEmbeddingAt L hL l y at hu
    have hkl := congrArg (listBlockOfAt L hL) hu
    simp only [listBlockOfAt_embedding] at hkl
    subst l
    have hxy := (listBlockEmbeddingAt L hL k).injective hu
    subst y
    rfl
  have hsurj : Function.Surjective f := by
    intro y
    let x := σ (listBlockEmbeddingAt M hM j y)
    let k := listBlockOfAt L hL x
    obtain ⟨i, hi⟩ := exists_listBlockCoordinateAt L hL x
    have hj : t k = j := by
      rw [← ht k i, permutedListBlockOf]
      change listBlockEmbeddingAt L hL k i = x at hi
      rw [hi, show σ.symm x = _ from σ.symm_apply_apply _, listBlockOfAt_embedding]
    let u : A := ⟨⟨k, hj⟩, i⟩
    refine ⟨u, (listBlockEmbeddingAt M hM j).injective ?_⟩
    rw [hf]
    change σ.symm (listBlockEmbeddingAt L hL k i) = listBlockEmbeddingAt M hM j y
    rw [hi]
    exact σ.symm_apply_apply _
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [Fintype.card_sigma] at hc
  rw [Finset.sum_subtype (p := fun k => t k = j) (Finset.univ.filter fun k => t k = j)
    (fun k => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ k))) (fun k => (L.get k).1)]
  simpa only [Fintype.card_fin] using hc

private theorem listParabolicCharacterAt_isClass (L : List (Pc g)) (hL : degL L = n)
    (h : ∀ p ∈ L, IsChar p.2) : IsClass (listParabolicCharacterAt L hL) := by
  obtain ⟨V, hV⟩ := isChar_listParabolicCharacterAt L hL h
  intro u v
  exact (hV _).symm.trans ((V.char_conj u v).trans (hV u))

/-- Nonzero cells with two target blocks inject into subsets of the
cuspidal source blocks having the rank of the first target block. -/
theorem card_nonzero_listParabolicPairing_twoBlocks_le
    (L : List (Pc g)) (p q : Pc g) (hL : degL L = p.1 + q.1)
    (hcus : ∀ z ∈ L, IsCusp z.2) (hp : IsChar p.2) (hq : IsChar q.2) :
    let M := [p, q]
    let hM : degL M = p.1 + q.1 := rfl
    let P := listParabolicAt L hL
    let Q := listParabolicAt M hM
    letI := mixedDoubleCosetFintype P Q
    Fintype.card {D : DoubleCoset.Quotient (P : Set (Gn g (p.1 + q.1))) Q //
      doubleCosetPairing P Q (listParabolicCharacterAt L hL) (listParabolicCharacterAt M hM) D.out ≠ 0} ≤
      Fintype.card {S : Finset (Fin L.length) // ∑ k ∈ S, (L.get k).1 = p.1} := by
  let M := [p, q]
  let hM : degL M = p.1 + q.1 := rfl
  let P := listParabolicAt L hL
  let Q := listParabolicAt M hM
  let D := DoubleCoset.Quotient (P : Set (Gn g (p.1 + q.1))) Q
  letI : Fintype D := mixedDoubleCosetFintype P Q
  let α := listParabolicCharacterAt L hL
  let β := listParabolicCharacterAt M hM
  let T := {d : D // doubleCosetPairing P Q α β d.out ≠ 0}
  have hα : IsClass α := listParabolicCharacterAt_isClass L hL fun z hz => by
    obtain ⟨V, _, hV⟩ := (hcus z hz).2.1
    exact ⟨V, hV⟩
  have hβ : IsClass β := listParabolicCharacterAt_isClass M hM fun z hz => by
    have he : z = p ∨ z = q := by simpa [M] using hz
    rcases he with rfl | rfl
    · exact hp
    · exact hq
  have hrep (d : T) : ∃ σ : Equiv.Perm (Fin (p.1 + q.1)),
      DoubleCoset.mk P Q (permutationUnit σ) = d.val := by
    obtain ⟨σ, hσ⟩ := exists_listParabolic_permutation_rep L M hL hM d.val.out
    exact ⟨σ, hσ.trans (DoubleCoset.out_eq' P Q d.val)⟩
  let σ (d : T) := (hrep d).choose
  have hσ (d : T) : DoubleCoset.mk P Q (permutationUnit (σ d)) = d.val := (hrep d).choose_spec
  let t (d : T) (k : Fin L.length) :=
    permutedListBlockOf M hM (σ d)
      (listBlockEmbeddingAt L hL k ⟨0, (hcus (L.get k) (List.get_mem L k)).1⟩)
  have ht (d : T) (k : Fin L.length) (i : Fin (L.get k).1) :
      permutedListBlockOf M hM (σ d) (listBlockEmbeddingAt L hL k i) = t d k := by
    letI : Fintype (doubleCosetOverlap P Q (permutationUnit (σ d))) := Fintype.ofFinite _
    have hn : doubleCosetPairing P Q α β (permutationUnit (σ d)) ≠ 0 := by
      rw [doubleCosetPairing_eq_of_mk_eq P Q α β hα hβ
        ((hσ d).trans (DoubleCoset.out_eq' P Q d.val).symm)]
      exact d.property
    exact permutedBlockOf_eq_of_pairing_ne_zero L M hL hM (σ d) k
      (hcus (L.get k) (List.get_mem L k)) hn i _
  let S (d : T) : {s : Finset (Fin L.length) // ∑ k ∈ s, (L.get k).1 = p.1} :=
    ⟨Finset.univ.filter fun k => t d k = 0,
      sum_ranks_of_block_allocation L M hL hM (σ d) (t d) (ht d) 0⟩
  change Fintype.card T ≤ _
  apply Fintype.card_le_of_injective S
  intro u v huv
  have htv (k : Fin L.length) : t u k = t v k := by
    have hS : (S u).val = (S v).val := congrArg Subtype.val huv
    have h : t u k = 0 ↔ t v k = 0 := by
      have he : k ∈ (S u).val ↔ k ∈ (S v).val := by rw [hS]
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using he
    apply Fin.ext
    have h₁ : (t u k).val < 2 := (t u k).isLt
    have h₂ : (t v k).val < 2 := (t v k).isLt
    simp only [Fin.ext_iff, Fin.val_zero] at h
    omega
  have he := listParabolic_coset_eq_of_targetBlocks_eq L M hL hM (σ u) (σ v) (fun i => by
    obtain ⟨j, hj⟩ := exists_listBlockCoordinateAt L hL i
    rw [← hj, ht u, ht v, htv])
  exact Subtype.ext ((hσ u).symm.trans (he.trans (hσ v)))

end GlobalTheory.GLq
