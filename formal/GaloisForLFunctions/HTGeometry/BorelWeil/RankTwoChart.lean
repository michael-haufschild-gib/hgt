import GaloisForLFunctions.HTGeometry.BorelWeil.CellAlgebra
import Mathlib.Tactic.FinCases

/-!
# The two charts of the flag variety of `GL(2)`

For `N = 2` the flag variety is the fibre `ℙ¹` itself: the Weyl group has two elements, the big cell
has a single coordinate `t`, and the two cell rings are the polynomials in `t` and in `t⁻¹`, with the
intersection the Laurent ring.  This is the base case of Bott's theorem, and the local model of the
fibre for every `N`.

## Main definitions

* `swapTwo` — the nontrivial element of the Weyl group of `GL(2)`.
* `tCoord` — the affine coordinate of the big cell.

## Main results

* `perm_fin_two_eq`, `univ_perm_fin_two`
* `cellSections_one_eq_adjoin` — the big cell ring is `k[t]`.
* `cellSections_swap_eq_adjoin` — the other cell ring is `k[t⁻¹]`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {k : Type*} [Field k] [Infinite k]

theorem zero_succ_lt_two : (0 : Fin 2).val + 1 < 2 := by norm_num

/-- The nontrivial element of the Weyl group of `GL(2)`. -/
noncomputable def swapTwo : Equiv.Perm (Fin 2) := swapNext (0 : Fin 2) zero_succ_lt_two

theorem fin_two_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  by_cases h : (x : ℕ) = 0
  · left
    exact Fin.ext (by simpa using h)
  · right
    have hx := x.isLt
    exact Fin.ext (by simp; omega)

theorem perm_fin_two_eq (σ : Equiv.Perm (Fin 2)) : σ = 1 ∨ σ = swapTwo := by
  classical
  have hone : (1 : Fin 2) = (⟨(0 : Fin 2).val + 1, zero_succ_lt_two⟩ : Fin 2) := rfl
  rcases fin_two_cases (σ 0) with h0 | h0
  · left
    have h1 : σ 1 = 1 := by
      rcases fin_two_cases (σ 1) with h1 | h1
      · exact absurd (σ.injective (h1.trans h0.symm)) (by decide)
      · exact h1
    refine Equiv.ext fun r => ?_
    rcases fin_two_cases r with hr | hr <;> rw [hr]
    · exact h0
    · exact h1
  · right
    have h1 : σ 1 = 0 := by
      rcases fin_two_cases (σ 1) with h1 | h1
      · exact h1
      · exact absurd (σ.injective (h1.trans h0.symm)) (by decide)
    refine Equiv.ext fun r => ?_
    rcases fin_two_cases r with hr | hr <;> rw [hr]
    · rw [h0, swapTwo, swapNext, Equiv.swap_apply_left]
      exact hone
    · rw [h1, swapTwo, swapNext, hone, Equiv.swap_apply_right]

theorem univ_perm_fin_two :
    (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, swapTwo} := by
  classical
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro σ _
    rcases perm_fin_two_eq σ with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    exact le_trans (Finset.card_insert_le _ _) (by simp)

/-- The affine coordinate of the big cell of the flag variety of `GL(2)`. -/
noncomputable def tCoord (k : Type*) [Field k] [Infinite k] : FlagLoc 2 k :=
  cellCoord (1 : Fin 2) (0 : Fin 2)

theorem cellCoord_fin_two_mem_adjoin (i j : Fin 2) :
    cellCoord (k := k) i j ∈ Algebra.adjoin k ({tCoord k} : Set (FlagLoc 2 k)) := by
  fin_cases i <;> fin_cases j
  · rw [cellCoord_diag]
    exact Subalgebra.one_mem _
  · rw [cellCoord_eq_zero_of_lt (by exact Fin.lt_def.mpr (by norm_num))]
    exact Subalgebra.zero_mem _
  · exact Algebra.subset_adjoin (Set.mem_singleton _)
  · rw [cellCoord_diag]
    exact Subalgebra.one_mem _

theorem cellCoordAlg_mem_adjoin (p : MvPolynomial (Fin 2 × Fin 2) k) :
    cellCoordAlg p ∈ Algebra.adjoin k ({tCoord k} : Set (FlagLoc 2 k)) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r =>
      rw [cellCoordAlg, MvPolynomial.aeval_C]
      exact Subalgebra.algebraMap_mem _ r
  | add q r hq hr =>
      rw [map_add]
      exact Subalgebra.add_mem _ hq hr
  | mul_X q ij hq =>
      rw [map_mul, cellCoordAlg, MvPolynomial.aeval_X]
      exact Subalgebra.mul_mem _ hq (cellCoord_fin_two_mem_adjoin ij.1 ij.2)

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {k : Type*} [Field k] [Infinite k]

theorem swapTwo_inv : (swapTwo)⁻¹ = swapTwo := by
  rw [swapTwo, swapNext, Equiv.swap_inv]

theorem tCoord_eq_cellCoord :
    tCoord k = cellCoord (⟨(0 : Fin 2).val + 1, zero_succ_lt_two⟩ : Fin 2) (0 : Fin 2) := rfl

/-- The inverse of the affine coordinate: the coordinate of the other chart. -/
noncomputable def tInv (k : Type*) [Field k] [Infinite k] : FlagLoc 2 k :=
  ((fibreCoord (1 : Equiv.Perm (Fin 2)) zero_succ_lt_two : (FlagLoc 2 k)ˣ) : FlagLoc 2 k)

theorem weylSubst_tCoord : weylSubst swapTwo (tCoord k) = tInv k := by
  rw [tCoord_eq_cellCoord, swapTwo, tInv]
  exact weylSubst_cellCoord_succ zero_succ_lt_two

theorem tCoord_mem_cellSubalg : tCoord k ∈ cellSubalg 2 k {(1 : Equiv.Perm (Fin 2))} :=
  cellCoord_mem_cellSections _ _

theorem tInv_mem_cellSubalg : tInv k ∈ cellSubalg 2 k {swapTwo} := by
  classical
  have h := weylSubst_mem_cellSections (k := k) swapTwo
    (I := ({(1 : Equiv.Perm (Fin 2))} : Finset (Equiv.Perm (Fin 2)))) (lam := fun _ => 0)
    tCoord_mem_cellSubalg
  have himg : ({(1 : Equiv.Perm (Fin 2))} : Finset (Equiv.Perm (Fin 2))).image
      (fun τ => swapTwo⁻¹ * τ) = {swapTwo} := by
    rw [Finset.image_singleton, mul_one, swapTwo_inv]
  rw [himg, weylSubst_tCoord] at h
  exact h

/-- **The big cell of the flag variety of `GL(2)` is the affine line.** -/
theorem cellSubalg_one_eq_adjoin :
    cellSubalg 2 k {(1 : Equiv.Perm (Fin 2))} = Algebra.adjoin k ({tCoord k} : Set (FlagLoc 2 k)) := by
  refine le_antisymm (fun x hx => ?_) (Algebra.adjoin_le ?_)
  · obtain ⟨p, hp⟩ := exists_cellCoordAlg_eq (mem_cellSubalg.mp hx)
    rw [hp]
    exact cellCoordAlg_mem_adjoin p
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact tCoord_mem_cellSubalg

/-- **The other cell of the flag variety of `GL(2)` is the opposite affine line.** -/
theorem cellSubalg_swap_eq_adjoin :
    cellSubalg 2 k {swapTwo} = Algebra.adjoin k ({tInv k} : Set (FlagLoc 2 k)) := by
  classical
  refine le_antisymm (fun x hx => ?_) (Algebra.adjoin_le ?_)
  · obtain ⟨p, hp⟩ := exists_weylSubst_cellCoordAlg_eq (mem_cellSubalg.mp hx)
    rw [hp, swapTwo_inv]
    have hmem : cellCoordAlg (k := k) p ∈ Algebra.adjoin k ({tCoord k} : Set (FlagLoc 2 k)) :=
      cellCoordAlg_mem_adjoin p
    have himg : (weylAlg (k := k) swapTwo) '' ({tCoord k} : Set (FlagLoc 2 k)) = {tInv k} := by
      rw [Set.image_singleton, weylAlg_apply, weylSubst_tCoord]
    have hmap := weylAlg_map_adjoin (k := k) swapTwo ({tCoord k} : Set (FlagLoc 2 k))
    rw [himg] at hmap
    rw [← hmap]
    exact ⟨cellCoordAlg p, hmem, rfl⟩
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact tInv_mem_cellSubalg

end GaloisForLFunctions.HTGeometry.BorelWeil
