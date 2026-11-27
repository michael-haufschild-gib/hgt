import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ListParabolicDiagonal
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CuspidalSplitCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitriangularParabolicCosets

/-! If a block meets both sides of a cut of the permuted flag, its split
radical lies in the overlap and has trivial projection to the permuted Levi. -/

noncomputable section
open scoped Classical

open GaloisForLFunctions

namespace GlobalTheory.GLq

variable {g n a b : ℕ} [Fact g.Prime]

section

variable (L : List (Pc g)) (hL : degL L = n)
variable (M : List (Pc g)) (hM : degL M = n) (σ : Equiv.Perm (Fin n))

/-- The block of the second flag containing a coordinate, in the ambient coordinates of the first. -/
def permutedListBlockOf (i : Fin n) : Fin M.length := listBlockOfAt M hM (σ.symm i)

variable (k : Fin L.length) (c : Fin M.length)

/-- The part of a block on or before a cut of the permuted flag. -/
def listBlockCut (i : Fin (L.get k).1) : Prop :=
  permutedListBlockOf M hM σ (listBlockEmbeddingAt L hL k i) ≤ c

omit [Fact g.Prime] in
theorem exists_listBlockCoordinateAt_of_eq {i : Fin n} {k : Fin L.length}
    (hi : listBlockOfAt L hL i = k) :
    ∃ j : Fin (L.get k).1, listBlockEmbeddingAt L hL k j = i := by
  subst k
  exact exists_listBlockCoordinateAt L hL i

private theorem listDiagonalUnitAt_apply_onBlock
    (x : listLeviGroup L) (l : Fin L.length) (i j : Fin (L.get l).1) :
    (listDiagonalUnitAt L hL x).val.val (listBlockEmbeddingAt L hL l i)
      (listBlockEmbeddingAt L hL l j) = (x l).val i j := by
  rw [← listBlockLeviAt_apply, listBlockLeviAt_listDiagonalUnitAt]

private theorem split_diagonal_apply_eq_one
    (e : Fin (a + b) ≃ Fin (L.get k).1)
    (he : ∀ i, listBlockCut L hL M hM σ k c (e i) ↔ i.val < a)
    (u : (twoBlockLevi (g := g) (a := a) (b := b)).ker)
    (i j : Fin n) (hij : permutedListBlockOf M hM σ j ≤ permutedListBlockOf M hM σ i) :
    (listDiagonalUnitAt L hL (Pi.mulSingle k (reindexUnit e u.val.val))).val.val i j =
      (1 : Mt g n) i j := by
  let x : listLeviGroup L := Pi.mulSingle k (reindexUnit e u.val.val)
  change (listDiagonalUnitAt L hL x).val.val i j = (1 : Mt g n) i j
  by_cases h : listBlockOfAt L hL i = listBlockOfAt L hL j
  · generalize hli : listBlockOfAt L hL i = l at h
    obtain ⟨r, hr⟩ := exists_listBlockCoordinateAt_of_eq L hL hli
    obtain ⟨s, hs⟩ := exists_listBlockCoordinateAt_of_eq L hL h.symm
    subst i
    subst j
    rw [listDiagonalUnitAt_apply_onBlock]
    have hId : ((1 : Gn g (L.get l).1)).val r s =
        (1 : Mt g n) (listBlockEmbeddingAt L hL l r) (listBlockEmbeddingAt L hL l s) := by
      simp only [Units.val_one, Matrix.one_apply, (listBlockEmbeddingAt L hL l).injective.eq_iff]
    rw [← hId]
    by_cases hl : l = k
    · subst l
      change ((Pi.mulSingle k (reindexUnit e u.val.val) : listLeviGroup L) k).val r s = _
      rw [Pi.mulSingle_eq_same]
      exact reindexedRadical_apply_eq_one_of_not_cross e he u r s
        (fun hp => hp.2 (hij.trans hp.1))
    · change ((Pi.mulSingle k (reindexUnit e u.val.val) : listLeviGroup L) l).val r s = _
      rw [Pi.mulSingle_eq_of_ne hl]
  · rw [listDiagonalUnitAt_eq_zero_offBlock L hL x i j h,
      Matrix.one_apply, if_neg (fun he => h (congrArg (listBlockOfAt L hL) he))]

/-- The radical of a split block maps into the overlap, with the chosen block
as its only nonidentity projection on the first Levi and with trivial second-Levi projection. -/
theorem exists_splitRadical_overlap
    (e : Fin (a + b) ≃ Fin (L.get k).1)
    (he : ∀ i, listBlockCut L hL M hM σ k c (e i) ↔ i.val < a) :
    ∃ m : (twoBlockLevi (g := g) (a := a) (b := b)).ker →*
      doubleCosetOverlap (listParabolicAt L hL) (listParabolicAt M hM) (permutationUnit σ),
      (∀ u l, listBlockLeviAt L hL l (m u).val =
        (Pi.mulSingle k (reindexUnit e u.val.val) : listLeviGroup L) l) ∧
      (∀ u l, listBlockLeviAt M hM l (doubleCosetOverlapConj
        (listParabolicAt L hL) (listParabolicAt M hM) (permutationUnit σ) (m u)) = 1) := by
  let w : Gn g n := permutationUnit σ
  let P := listParabolicAt L hL
  let Q := listParabolicAt M hM
  let N := (twoBlockLevi (g := g) (a := a) (b := b)).ker
  let ι : N →* Gn g (a + b) := (twoBlockParabolic g a b).subtype.comp N.subtype
  let d : N →* P := (listDiagonalUnitAt L hL).comp
    ((MonoidHom.mulSingle (fun l : Fin L.length => Gn g (L.get l).1) k).comp ((reindexUnit e).comp ι))
  have hentry (u : N) (i j : Fin n) (hij : listBlockOfAt M hM j ≤ listBlockOfAt M hM i) :
      (w⁻¹ * (d u).val * w : Gn g n).val i j = (1 : Mt g n) i j := by
    rw [permutationUnit_conj_apply]
    have hp : permutedListBlockOf M hM σ (σ j) ≤ permutedListBlockOf M hM σ (σ i) := by
      simpa only [permutedListBlockOf, σ.symm_apply_apply] using hij
    change (listDiagonalUnitAt L hL (Pi.mulSingle k (reindexUnit e u.val.val))).val.val (σ i) (σ j) = _
    rw [split_diagonal_apply_eq_one L hL M hM σ k c e he u (σ i) (σ j) hp]
    simp only [Matrix.one_apply, σ.injective.eq_iff]
  have hmem (u : N) : d u ∈ doubleCosetOverlap P Q w := by
    apply (mem_doubleCosetOverlap P Q w (d u)).mpr
    apply (mem_listParabolicAt_iff M hM _).mpr
    intro i j h
    rw [hentry u i j h.le, Matrix.one_apply, if_neg]
    exact fun hi => (ne_of_lt h) (congrArg (listBlockOfAt M hM) hi.symm)
  let m : N →* doubleCosetOverlap P Q w :=
    { toFun := fun u => ⟨d u, hmem u⟩
      map_one' := Subtype.ext (map_one d)
      map_mul' := fun u v => Subtype.ext (map_mul d u v) }
  refine ⟨m, fun u l => ?_, fun u l => ?_⟩
  · exact listBlockLeviAt_listDiagonalUnitAt L hL (Pi.mulSingle k (reindexUnit e u.val.val)) l
  · apply Units.ext
    ext i j
    rw [listBlockLeviAt_apply]
    change (w⁻¹ * (d u).val * w : Gn g n).val (listBlockEmbeddingAt M hM l i) (listBlockEmbeddingAt M hM l j) = _
    rw [hentry u _ _ (by rw [listBlockOfAt_embedding, listBlockOfAt_embedding])]
    simp only [Units.val_one, Matrix.one_apply, (listBlockEmbeddingAt M hM l).injective.eq_iff]

end

end GlobalTheory.GLq
