import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CuspidalSupportNorm
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.SelectedBlockCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraWeightNonneg

/-! For distinct cuspidal blocks, reordering the blocks gives the same
irreducible Harish–Chandra product. The block permutation gives an overlap
on which the two inducing characters agree. -/

noncomputable section
open GaloisForLFunctions
open scoped Classical

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

omit [Fact g.Prime] in
private theorem exists_matching_indices (L M : List (Pc g)) (hperm : L.Perm M)
    (hL : L.Nodup) (hM : M.Nodup) :
    ∃ e : Fin L.length ≃ Fin M.length, ∀ k, L.get k = M.get (e k) := by
  have hm (k : Fin L.length) : ∃ j : Fin M.length, L.get k = M.get j := by
    have hmem := hperm.mem_iff.mp (List.get_mem L k)
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hmem
    exact ⟨j, hj.symm⟩
  let f (k : Fin L.length) := (hm k).choose
  have hf (k : Fin L.length) : L.get k = M.get (f k) := (hm k).choose_spec
  have hinj : Function.Injective f := by
    intro a b h
    exact (List.nodup_iff_injective_get.mp hL) ((hf a).trans ((congrArg M.get h).trans (hf b).symm))
  have hsurj : Function.Surjective f := by
    intro j
    have hmem := hperm.mem_iff.mpr (List.get_mem M j)
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hmem
    exact ⟨k, (List.nodup_iff_injective_get.mp hM) ((hf k).symm.trans hk)⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

omit [Fact g.Prime] in
private theorem exists_matching_permutation (L M : List (Pc g)) (hL : degL L = n) (hM : degL M = n)
    (e : Fin L.length ≃ Fin M.length) (he : ∀ k, L.get k = M.get (e k)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, e (listBlockOfAt L hL i) = permutedListBlockOf M hM σ i := by
  let cL := listBlockCoordinateEquiv L hL
  let cM := listBlockCoordinateEquiv M hM
  let d (k : Fin L.length) : Fin (L.get k).1 ≃ Fin (M.get (e k)).1 :=
    finCongr (congrArg Sigma.fst (he k))
  let E := Equiv.sigmaCongr
    (β₁ := fun k => Fin (L.get k).1) (β₂ := fun j => Fin (M.get j).1) e d
  let σ := (cL.symm.trans (E.trans cM)).symm
  refine ⟨σ, fun i => ?_⟩
  obtain ⟨⟨k, j⟩, rfl⟩ := cL.surjective i
  change e (listBlockOfAt L hL (cL ⟨k, j⟩)) =
    listBlockOfAt M hM (cM (E (cL.symm (cL ⟨k, j⟩))))
  rw [cL.symm_apply_apply]
  change e (listBlockOfAt L hL (listBlockCoordinateEquiv L hL ⟨k, j⟩)) =
    listBlockOfAt M hM (listBlockCoordinateEquiv M hM ⟨e k, d k j⟩)
  rw [listBlockCoordinateEquiv_apply, listBlockCoordinateEquiv_apply, listBlockOfAt_embedding,
    listBlockOfAt_embedding]

private theorem character_isClass {G : Type} [Group G] {χ : G → ℂ} (hχ : IsChar χ) :
    IsClass χ := by
  obtain ⟨V, hV⟩ := hχ
  intro x y
  exact (hV (y * x * y⁻¹)).symm.trans ((V.char_conj x y).trans (hV x))

private theorem cuspidal_character_reindex {p q : Pc g} (h : p = q) (hp : IsCusp p.2)
    (e : Fin p.1 ≃ Fin q.1) (u : Gn g p.1) : q.2 (reindexUnit e u) = p.2 u := by
  subst q
  rw [reindexUnit_perm]
  exact character_isClass (isChar_of_cuspidal hp) _ _

private theorem matched_overlap_agrees (L M : List (Pc g)) (hL : degL L = n) (hM : degL M = n)
    (σ : Equiv.Perm (Fin n)) (e : Fin L.length ≃ Fin M.length)
    (he : ∀ i, e (listBlockOfAt L hL i) = permutedListBlockOf M hM σ i)
    (hlab : ∀ k, L.get k = M.get (e k)) (hcus : ∀ p ∈ L, IsCusp p.2)
    (u : doubleCosetOverlap (listParabolicAt L hL) (listParabolicAt M hM) (permutationUnit σ)) :
    listParabolicCharacterAt M hM
      (doubleCosetOverlapConj (listParabolicAt L hL) (listParabolicAt M hM) (permutationUnit σ) u) =
      listParabolicCharacterAt L hL u.val := by
  let C := doubleCosetOverlapConj (listParabolicAt L hL) (listParabolicAt M hM) (permutationUnit σ)
  simp only [listParabolicCharacterAt_eq_prod]
  rw [← Equiv.prod_comp e (fun k => (M.get k).2 (listBlockLeviAt M hM k (C u)))]
  refine Finset.prod_congr rfl fun k _ => ?_
  let d := matchedBlockCoordinates L M hL hM σ e he k
  have hcoord (i : Fin (M.get (e k)).1) :
      σ (listBlockEmbeddingAt M hM (e k) i) = listBlockEmbeddingAt L hL k (d.symm i) := by
    have hd := matchedBlockCoordinates_apply L M hL hM σ e he k (d.symm i)
    change σ (listBlockEmbeddingAt M hM (e k) (d (d.symm i))) = _ at hd
    rwa [d.apply_symm_apply] at hd
  have hlev :
      listBlockLeviAt M hM (e k) (C u) = reindexUnit d (listBlockLeviAt L hL k u.val) := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    rw [listBlockLeviAt_apply, reindexUnit_apply, listBlockLeviAt_apply]
    change ((permutationUnit σ)⁻¹ * u.val.val * permutationUnit σ).val
      (listBlockEmbeddingAt M hM (e k) i) (listBlockEmbeddingAt M hM (e k) j) = _
    rw [permutationUnit_conj_apply, hcoord i, hcoord j]
  change (M.get (e k)).2 (listBlockLeviAt M hM (e k) (C u)) =
    (L.get k).2 (listBlockLeviAt L hL k u.val)
  rw [hlev]
  exact cuspidal_character_reindex (hlab k) (hcus _ (List.get_mem L k)) d _

private theorem overlap_pairing_nonneg {G : Type} [Group G] [Fintype G]
    (P Q : Subgroup G) {α : P → ℂ} {β : Q → ℂ} (hα : IsChar α) (hβ : IsChar β)
    (w : G) [Fintype (doubleCosetOverlap P Q w)] :
    0 ≤ (doubleCosetPairing P Q α β w).re := by
  obtain ⟨V, hV⟩ := hα
  obtain ⟨W, hW⟩ := hβ
  let O := doubleCosetOverlap P Q w
  let C := doubleCosetOverlapConj P Q w
  let ρ : Representation ℂ O V := (V.ρ : Representation ℂ P V).comp O.subtype
  let σ : Representation ℂ O W := (W.ρ : Representation ℂ Q W).comp C
  rw [← funext hV, ← funext hW, doubleCosetPairing_eq_pairing]
  change 0 ≤ (characterPairing O ρ.character σ.character).re
  rw [representationCharacterPairing_eq_finrank, Complex.natCast_re]
  exact Nat.cast_nonneg _

private theorem overlap_pairing_pos {G : Type} [Group G] [Fintype G]
    (P Q : Subgroup G) {α : P → ℂ} {β : Q → ℂ} (hα : IsChar α) (w : G)
    [Fintype (doubleCosetOverlap P Q w)]
    (ha : α 1 ≠ 0) (he : ∀ u : doubleCosetOverlap P Q w,
      β (doubleCosetOverlapConj P Q w u) = α u.val) :
    0 < (doubleCosetPairing P Q α β w).re := by
  let O := doubleCosetOverlap P Q w
  let f (u : O) := α u.val
  have hf : f ∈ virtualCharacterGroup O := by
    obtain ⟨V, hV⟩ := hα
    let W := FDRep.of (V.ρ.comp O.subtype)
    exact AddSubgroup.subset_closure ⟨W, funext fun u => hV u.val⟩
  have hsum :
      (∑ u : O, β (doubleCosetOverlapConj P Q w u) * α u.val⁻¹) =
        ((∑ u : O, Complex.normSq (f u) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [he]
    change f u * f u⁻¹ = _
    rw [CuspGL.virtualCharacter_inv_eq_conj hf, Complex.mul_conj]
  rw [doubleCosetPairing_eq_pairing, characterPairing]
  change 0 < ((Nat.card O : ℂ)⁻¹ *
    ∑ u : O, β (doubleCosetOverlapConj P Q w u) * α u.val⁻¹).re
  rw [hsum, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  refine mul_pos (inv_pos.mpr (by exact_mod_cast Nat.card_pos (α := O))) ?_
  have hpos : 0 < Complex.normSq (f 1) := by
    refine lt_of_le_of_ne (Complex.normSq_nonneg _) fun h => ha ?_
    exact Complex.normSq_eq_zero.mp h.symm
  exact hpos.trans_le (Finset.single_le_sum (fun u _ => Complex.normSq_nonneg (f u))
    (Finset.mem_univ (1 : O)))

/-- A permutation of the inducing list preserves its Harish–Chandra product
when the cuspidal blocks are pairwise distinct. -/
theorem hcL_eq_of_perm_cuspidal_nodup (L M : List (Pc g)) (hL : degL L = n) (hM : degL M = n)
    (hperm : L.Perm M) (hndL : L.Nodup) (hndM : M.Nodup)
    (hcusL : ∀ p ∈ L, IsCusp p.2) (hcusM : ∀ p ∈ M, IsCusp p.2) :
    hcL L n = hcL M n := by
  obtain ⟨e, he⟩ := exists_matching_indices L M hperm hndL hndM
  obtain ⟨σ, hσ⟩ := exists_matching_permutation L M hL hM e he
  let P := listParabolicAt L hL
  let Q := listParabolicAt M hM
  let q := DoubleCoset.mk P Q (permutationUnit (g := g) σ)
  let α := listParabolicCharacterAt L hL
  let β := listParabolicCharacterAt M hM
  have hLc (p : Pc g) (hp : p ∈ L) : IsChar p.2 := isChar_of_cuspidal (hcusL p hp)
  have hMc (p : Pc g) (hp : p ∈ M) : IsChar p.2 := isChar_of_cuspidal (hcusM p hp)
  have hα : IsChar α := isChar_listParabolicCharacterAt L hL hLc
  have hβ : IsChar β := isChar_listParabolicCharacterAt M hM hMc
  have hα1 : α 1 ≠ 0 := by
    change listParabolicCharacterAt L hL 1 ≠ 0
    rw [listParabolicCharacterAt_eq_prod, Finset.prod_ne_zero_iff]
    intro k _
    rw [map_one]
    obtain ⟨d, hd, hχ⟩ := irr_degree_pos (hcusL _ (List.get_mem L k)).2.1
    rw [hχ]
    exact Nat.cast_ne_zero.mpr hd.ne'
  letI := mixedDoubleCosetFintype P Q
  let F (z : DoubleCoset.Quotient (P : Set (Gn g n)) Q) := doubleCosetPairing P Q α β z.out
  have hq : 0 < (F q).re := by
    have eq := doubleCosetPairing_eq_of_mk_eq P Q α β (character_isClass hα)
      (character_isClass hβ) (DoubleCoset.out_eq' P Q q)
    change 0 < (doubleCosetPairing P Q α β q.out).re
    rw [eq]
    exact overlap_pairing_pos P Q hα (permutationUnit σ) hα1
      (matched_overlap_agrees L M hL hM σ e hσ he hcusL)
  have hpos : 0 < (characterPairing (Gn g n) (hcL L n) (hcL M n)).re := by
    rw [characterPairing_hcL_eq_sum_doubleCosets L M hL hM hLc hMc]
    change 0 < (∑ z, F z).re
    rw [Complex.re_sum]
    exact hq.trans_le (Finset.single_le_sum (fun z _ => overlap_pairing_nonneg P Q hα hβ z.out)
      (Finset.mem_univ q))
  obtain ⟨V, hV, heV⟩ := isIrr_hcL_of_nodup L hL hcusL hndL
  obtain ⟨W, hW, heW⟩ := isIrr_hcL_of_nodup M hM hcusM hndM
  have hv : hcL L n ∈ CuspGL.simpleCharacterSet (Gn g n) := ⟨V, hV, funext heV⟩
  have hw : hcL M n ∈ CuspGL.simpleCharacterSet (Gn g n) := ⟨W, hW, funext heW⟩
  by_contra hn
  rw [CuspGL.pairing_simple hv hw, if_neg hn, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

end GlobalTheory.GLq
