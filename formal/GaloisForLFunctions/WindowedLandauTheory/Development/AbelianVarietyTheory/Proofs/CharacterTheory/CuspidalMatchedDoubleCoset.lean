import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ListParabolicBlockMatching
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterNorm
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! With matched blocks, the overlap pairing factors through their common
Levi group. One unequal pair of cuspidal characters forces the pairing to vanish. -/

noncomputable section
open scoped Classical

open GaloisForLFunctions

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

/-- Collect the diagonal-block projections into the full Levi group. -/
def listLeviProjectionAt (L : List (Pc g)) (hL : degL L = n) :
    listParabolicAt L hL →* listLeviGroup L where
  toFun u k := listBlockLeviAt L hL k u
  map_one' := funext fun k => map_one (listBlockLeviAt L hL k)
  map_mul' u v := funext fun k => map_mul (listBlockLeviAt L hL k) u v

private theorem block_sum_zero_of_distinct (p q : Pc g) (hp : IsIrr p.2) (hq : IsIrr q.2)
    (hne : p ≠ q) (e : Fin p.1 ≃ Fin q.1) :
    ∑ x : Gn g p.1, q.2 (reindexUnit e x) * p.2 x⁻¹ = 0 := by
  rcases p with ⟨a, α⟩
  rcases q with ⟨b, β⟩
  have he : a = b := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst b
  have hne' : α ≠ β := fun h => hne (congrArg (fun χ : Gn g a → ℂ => (⟨a, χ⟩ : Pc g)) h)
  obtain ⟨V, hV, hcV⟩ := hp
  obtain ⟨W, hW, hcW⟩ := hq
  have hβ (x : Gn g a) : β (reindexUnit e x) = β x :=
    (congrArg β (reindexUnit_perm e x)).trans
      ((hcW _).symm.trans ((W.char_conj x _).trans (hcW x)))
  have hp : α ∈ CuspGL.simpleCharacterSet (Gn g a) := ⟨V, hV, funext hcV⟩
  have hq : β ∈ CuspGL.simpleCharacterSet (Gn g a) := ⟨W, hW, funext hcW⟩
  have hz := (CuspGL.pairing_simple hp hq).trans (if_neg hne')
  have hc : (Nat.card (Gn g a) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hsum : ∑ x : Gn g a, β x * α x⁻¹ = 0 :=
    (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hc)
  change ∑ x : Gn g a, β (reindexUnit e x) * α x⁻¹ = 0
  simpa only [hβ] using hsum

section

variable (L M : List (Pc g)) (hL : degL L = n) (hM : degL M = n) (σ : Equiv.Perm (Fin n))
variable (e : Fin L.length ≃ Fin M.length)
variable (he : ∀ i, e (listBlockOfAt L hL i) = permutedListBlockOf M hM σ i)

include he in
private theorem listDiagonal_mem_overlap (x : listLeviGroup L) :
    listDiagonalUnitAt L hL x ∈
      doubleCosetOverlap (listParabolicAt L hL) (listParabolicAt M hM) (permutationUnit σ) := by
  let w : Gn g n := permutationUnit σ
  apply (mem_doubleCosetOverlap _ _ w _).mpr
  apply (mem_listParabolicAt_iff M hM _).mpr
  intro i j hij
  have h (r : Fin n) : e (listBlockOfAt L hL (σ r)) = listBlockOfAt M hM r := by
    simpa only [permutedListBlockOf, σ.symm_apply_apply] using he (σ r)
  have hn : listBlockOfAt L hL (σ i) ≠ listBlockOfAt L hL (σ j) := fun h' =>
    (ne_of_lt hij) ((h j).symm.trans ((congrArg e h'.symm).trans (h i)))
  rw [permutationUnit_conj_apply]
  exact listDiagonalUnitAt_eq_zero_offBlock L hL x (σ i) (σ j) hn

private theorem matched_levi_projection
    (u : doubleCosetOverlap (listParabolicAt L hL) (listParabolicAt M hM) (permutationUnit σ))
    (k : Fin L.length) :
    listBlockLeviAt M hM (e k) (doubleCosetOverlapConj (listParabolicAt L hL)
      (listParabolicAt M hM) (permutationUnit σ) u) =
    reindexUnit (matchedBlockCoordinates L M hL hM σ e he k) (listBlockLeviAt L hL k u.val) := by
  let d := matchedBlockCoordinates L M hL hM σ e he k
  let w : Gn g n := permutationUnit σ
  have h (i : Fin (M.get (e k)).1) :
      σ (listBlockEmbeddingAt M hM (e k) i) = listBlockEmbeddingAt L hL k (d.symm i) := by
    have h' := matchedBlockCoordinates_apply L M hL hM σ e he k (d.symm i)
    change σ (listBlockEmbeddingAt M hM (e k) (d (d.symm i))) = _ at h'
    rwa [d.apply_symm_apply] at h'
  apply Units.ext
  apply Matrix.ext
  intro i j
  rw [listBlockLeviAt_apply, reindexUnit_apply, listBlockLeviAt_apply]
  change (w⁻¹ * u.val.val * w : Gn g n).val (listBlockEmbeddingAt M hM (e k) i)
    (listBlockEmbeddingAt M hM (e k) j) = _
  rw [permutationUnit_conj_apply, h i, h j]

include he in
/-- An aligned cell has vanishing pairing whenever two matched labels differ. -/
theorem listParabolicPairing_eq_zero_of_matched_ne
    [Fintype (doubleCosetOverlap (listParabolicAt L hL) (listParabolicAt M hM) (permutationUnit σ))]
    (hLi : ∀ k : Fin L.length, IsIrr (L.get k).2) (hMi : ∀ k : Fin M.length, IsIrr (M.get k).2)
    (k : Fin L.length) (hne : L.get k ≠ M.get (e k)) :
    doubleCosetPairing (listParabolicAt L hL) (listParabolicAt M hM)
      (listParabolicCharacterAt L hL) (listParabolicCharacterAt M hM) (permutationUnit σ) = 0 := by
  let P := listParabolicAt L hL
  let Q := listParabolicAt M hM
  let w : Gn g n := permutationUnit σ
  let O := doubleCosetOverlap P Q w
  let C := doubleCosetOverlapConj P Q w
  let π : O →* listLeviGroup L := (listLeviProjectionAt L hL).comp O.subtype
  have hs : Function.Surjective π := fun x =>
    ⟨⟨listDiagonalUnitAt L hL x, listDiagonal_mem_overlap L M hL hM σ e he x⟩,
      funext fun l => listBlockLeviAt_listDiagonalUnitAt L hL x l⟩
  let δ (l : Fin L.length) := matchedBlockCoordinates L M hL hM σ e he l
  let f (l : Fin L.length) (z : Gn g (L.get l).1) :=
    (M.get (e l)).2 (reindexUnit (δ l) z) * (L.get l).2 z⁻¹
  let F (z : listLeviGroup L) := ∏ l : Fin L.length, f l (z l)
  have hF (u : O) :
      listParabolicCharacterAt M hM (C u) * listParabolicCharacterAt L hL u.val⁻¹ = F (π u) := by
    simp only [listParabolicCharacterAt_eq_prod]
    rw [← Equiv.prod_comp e (fun l => (M.get l).2 (listBlockLeviAt M hM l (C u)))]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    change (M.get (e l)).2 (listBlockLeviAt M hM (e l) (C u)) *
      (L.get l).2 (listBlockLeviAt L hL l u.val⁻¹) = f l (π u l)
    rw [map_inv, matched_levi_projection L M hL hM σ e he u l]
    rfl
  have hzero : (∑ z : listLeviGroup L, F z) = 0 := by
    change (∑ z : listLeviGroup L, ∏ l : Fin L.length, f l (z l)) = 0
    rw [← Fintype.prod_sum f]
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    exact block_sum_zero_of_distinct _ _ (hLi k) (hMi (e k)) hne (δ k)
  rw [doubleCosetPairing_eq_pairing]
  change (Nat.card O : ℂ)⁻¹ * (∑ u : O,
    listParabolicCharacterAt M hM (C u) * listParabolicCharacterAt L hL u.val⁻¹) = 0
  rw [Finset.sum_congr rfl (fun u _ => hF u), sum_comp_surjective_hom π hs F, hzero, mul_zero, mul_zero]

end

end GlobalTheory.GLq
