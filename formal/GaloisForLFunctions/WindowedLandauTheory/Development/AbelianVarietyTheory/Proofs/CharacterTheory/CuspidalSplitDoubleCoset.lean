import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ListParabolicSplitRadical
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ListParabolicDoubleCosets

/-! On a double coset splitting a block, the other parabolic character is
constant along the split radical and the cuspidal block character averages to zero. -/

noncomputable section
open scoped Classical

open GaloisForLFunctions

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

/-- A permutation that splits a cuspidal block has zero overlap pairing. -/
theorem listParabolicPairing_eq_zero_of_split (L M : List (Pc g)) (hL : degL L = n)
    (hM : degL M = n) (σ : Equiv.Perm (Fin n)) (k : Fin L.length) (hχ : IsCusp (L.get k).2)
    [Fintype (doubleCosetOverlap (listParabolicAt L hL) (listParabolicAt M hM) (permutationUnit σ))]
    (i j : Fin (L.get k).1)
    (hij : permutedListBlockOf M hM σ (listBlockEmbeddingAt L hL k i) <
      permutedListBlockOf M hM σ (listBlockEmbeddingAt L hL k j)) :
    doubleCosetPairing (listParabolicAt L hL) (listParabolicAt M hM)
      (listParabolicCharacterAt L hL) (listParabolicCharacterAt M hM) (permutationUnit σ) = 0 := by
  let c := permutedListBlockOf M hM σ (listBlockEmbeddingAt L hL k i)
  let p := listBlockCut L hL M hM σ k c
  obtain ⟨a, b, ha, hb, e, he⟩ := exists_fin_split p ⟨i, le_rfl⟩ ⟨j, not_le_of_gt hij⟩
  let P := listParabolicAt L hL
  let Q := listParabolicAt M hM
  let w : Gn g n := permutationUnit σ
  let O := doubleCosetOverlap P Q w
  let N := (twoBlockLevi (g := g) (a := a) (b := b)).ker
  letI : Fintype N := Fintype.ofFinite N
  let C := doubleCosetOverlapConj P Q w
  let α := listParabolicCharacterAt L hL
  let β := listParabolicCharacterAt M hM
  let χ := (L.get k).2
  let π (l : Fin L.length) := listBlockLeviAt L hL l
  obtain ⟨m, hleft, hright⟩ := exists_splitRadical_overlap L hL M hM σ k c e he
  apply doubleCosetPairing_eq_zero_of_overlap_average P Q α β w m
  intro u
  let rest : ℂ := ∏ l ∈ Finset.univ.erase k, (L.get l).2 (π l u.val⁻¹)
  let t := π k u.val⁻¹
  have hr (z : N) : β (C (m z * u)) = β (C u) := by
    rw [map_mul]
    simp only [β, listParabolicCharacterAt_eq_prod]
    refine Finset.prod_congr rfl fun l _ => ?_
    have hz : listBlockLeviAt M hM l (C (m z)) = 1 := hright z l
    rw [map_mul, hz, one_mul]
  have hl (z : N) (l : Fin L.length) :
      π l (m z * u).val⁻¹ =
        π l u.val⁻¹ * ((Pi.mulSingle k (reindexUnit e z.val.val) : listLeviGroup L) l)⁻¹ := by
    change π l ((m z).val * u.val)⁻¹ = _
    simp only [mul_inv_rev, map_mul, map_inv]
    exact congrArg (fun y : Gn g (L.get l).1 => (π l u.val)⁻¹ * y⁻¹) (hleft z l)
  have hα (z : N) : α (m z * u).val⁻¹ = χ (t * reindexUnit e (z⁻¹ : N).val.val) * rest := by
    change listParabolicCharacterAt L hL (m z * u).val⁻¹ = _
    rw [listParabolicCharacterAt_eq_prod,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
    apply congrArg₂ (· * ·)
    · rw [hl z k, Pi.mulSingle_eq_same, ← map_inv]
      rfl
    · apply Finset.prod_congr rfl
      intro l hlmem
      rw [hl z l, Pi.mulSingle_eq_of_ne (Finset.mem_erase.mp hlmem).1, inv_one, mul_one]
  calc
    _ = ∑ z : N, (β (C u) * rest) * χ (t * reindexUnit e (z⁻¹ : N).val.val) := by
      refine Finset.sum_congr rfl fun z _ => ?_
      change β (C (m z * u)) * α (m z * u).val⁻¹ = _
      rw [hr, hα]
      ring
    _ = (β (C u) * rest) * ∑ z : N, χ (t * reindexUnit e (z⁻¹ : N).val.val) :=
      (Finset.mul_sum _ _ _).symm
    _ = (β (C u) * rest) * ∑ z : N, χ (t * reindexUnit e z.val.val) :=
      congrArg ((β (C u) * rest) * ·)
        (Equiv.sum_comp (Equiv.inv N) (fun z : N => χ (t * reindexUnit e z.val.val)))
    _ = 0 := by rw [sum_cuspidal_reindexed_radical_translate_eq_zero hχ ha hb e t, mul_zero]

end GlobalTheory.GLq
