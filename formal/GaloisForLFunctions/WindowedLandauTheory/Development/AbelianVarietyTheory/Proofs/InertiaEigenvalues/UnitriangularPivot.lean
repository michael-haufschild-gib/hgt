import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCharacter
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Clearing the first column and its pivot row using upper unitriangular
operations. -/

noncomputable section
open scoped Classical

open Matrix
open WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

variable {g : ℕ} [Fact g.Prime]

private def addSquareZero {n : ℕ} (R : Mt g n) (hR : R * R = 0) : Gn g n where
  val := 1 + R
  inv := 1 - R
  val_inv := by
    rw [add_mul, one_mul, mul_sub, mul_one, hR, sub_zero, sub_add_cancel]
  inv_val := by
    rw [sub_mul, one_mul, mul_add, mul_one, hR, add_zero, add_sub_cancel_right]

private theorem addSquareZero_mem {n : ℕ} (R : Mt g n) (hR : R * R = 0)
    (h : ∀ i j : Fin n, j ≤ i → R i j = 0) :
    addSquareZero R hR ∈ upperUnitriangular g n := by
  intro i j
  change ((j < i → (1 + R) i j = 0) ∧ (i = j → (1 + R) i j = 1))
  constructor
  · intro e
    rw [Matrix.add_apply, h i j e.le, Matrix.one_apply_ne (ne_of_gt e), add_zero]
  · rintro rfl
    rw [Matrix.add_apply, h i i le_rfl, Matrix.one_apply_eq, add_zero]

private theorem first_column_nonzero {n : ℕ} (A : Gn g (n + 1)) :
    ∃ i : Fin (n + 1), (A : Mt g (n + 1)) i 0 ≠ 0 := by
  by_contra h
  push Not at h
  have hd := (Matrix.isUnits_det_units A).ne_zero
  rw [Matrix.det_succ_column_zero] at hd
  exact hd (Finset.sum_eq_zero fun i _ => by rw [h i, mul_zero, zero_mul])

/-- The bottommost nonzero entry of the first column can be isolated from
its row and column by upper unitriangular operations. -/
theorem exists_unitriangular_pivot {n : ℕ} (A : Gn g (n + 1)) :
    ∃ (a b : upperUnitriangular g (n + 1)) (p : Fin (n + 1)) (v : (ZMod g)ˣ),
      let B : Mt g (n + 1) := ((a : Gn g (n + 1)) * A * b : Gn g (n + 1))
      B p 0 = v ∧ (∀ i, i ≠ p → B i 0 = 0) ∧ (∀ j, j ≠ 0 → B p j = 0) := by
  let M := (A : Mt g (n + 1))
  let S := Finset.univ.filter fun i : Fin (n + 1) => M i 0 ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := first_column_nonzero A
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let p := S.max' hS
  have hp : M p 0 ≠ 0 := (Finset.mem_filter.mp (S.max'_mem hS)).2
  let r (i : Fin (n + 1)) : ZMod g := if i < p then -(M i 0 / M p 0) else 0
  have hr : r p = 0 := if_neg (lt_irrefl p)
  let R : Mt g (n + 1) := vecMulVec r (Pi.single p 1)
  have hR : R * R = 0 := by
    change vecMulVec r (Pi.single p 1) * vecMulVec r (Pi.single p 1) = 0
    rw [vecMulVec_mul_vecMulVec, single_one_dotProduct, hr, zero_smul, vecMulVec_zero]
  have hRu (i j : Fin (n + 1)) (h : j ≤ i) : R i j = 0 := by
    change r i * (Pi.single p 1 : Fin (n + 1) → ZMod g) j = 0
    by_cases e : j = p
    · subst j
      rw [show r i = 0 from if_neg (not_lt_of_ge h), zero_mul]
    · rw [Pi.single_eq_of_ne e, mul_zero]
  let a : upperUnitriangular g (n + 1) := ⟨addSquareZero R hR, addSquareZero_mem R hR hRu⟩
  let B : Mt g (n + 1) := ((a : Gn g (n + 1)) * A : Gn g (n + 1))
  have hB (i j : Fin (n + 1)) : B i j = M i j + r i * M p j := by
    change ((1 + vecMulVec r (Pi.single p 1)) * M) i j = _
    rw [Matrix.add_mul, Matrix.one_mul, vecMulVec_mul, single_one_vecMul]
    rfl
  have hBp : B p 0 = M p 0 := by rw [hB, hr, zero_mul, add_zero]
  have hB₀ (i : Fin (n + 1)) (hi : i ≠ p) : B i 0 = 0 := by
    rw [hB]
    rcases lt_or_gt_of_ne hi with h | h
    · rw [show r i = -(M i 0 / M p 0) from if_pos h, neg_mul, div_mul_cancel₀ _ hp, add_neg_cancel]
    · have hM : M i 0 = 0 := by
        by_contra hn
        exact (not_le_of_gt h) (S.le_max' i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hn⟩))
      rw [show r i = 0 from if_neg (not_lt_of_ge h.le), zero_mul, add_zero, hM]
  let s (j : Fin (n + 1)) : ZMod g := if 0 < j then -(B p j / M p 0) else 0
  have hs : s 0 = 0 := if_neg (lt_irrefl 0)
  let C : Mt g (n + 1) := vecMulVec (Pi.single 0 1) s
  have hC : C * C = 0 := by
    change vecMulVec (Pi.single (0 : Fin (n + 1)) 1) s *
      vecMulVec (Pi.single (0 : Fin (n + 1)) 1) s = 0
    rw [vecMulVec_mul_vecMulVec, dotProduct_single_one, hs, zero_smul, vecMulVec_zero]
  have hCu (i j : Fin (n + 1)) (h : j ≤ i) : C i j = 0 := by
    change (Pi.single 0 1 : Fin (n + 1) → ZMod g) i * s j = 0
    by_cases e : i = 0
    · subst i
      rw [show s j = 0 from if_neg (not_lt_of_ge h), mul_zero]
    · rw [Pi.single_eq_of_ne e, zero_mul]
  let b : upperUnitriangular g (n + 1) := ⟨addSquareZero C hC, addSquareZero_mem C hC hCu⟩
  let D : Mt g (n + 1) := ((a : Gn g (n + 1)) * A * b : Gn g (n + 1))
  have hD (i j : Fin (n + 1)) : D i j = B i j + B i 0 * s j := by
    change (B * (1 + vecMulVec (Pi.single (0 : Fin (n + 1)) 1) s)) i j = _
    rw [Matrix.mul_add, Matrix.mul_one, mul_vecMulVec, mulVec_single_one]
    rfl
  refine ⟨a, b, p, Units.mk0 (M p 0) hp, ?_⟩
  change D p 0 = M p 0 ∧ (∀ i, i ≠ p → D i 0 = 0) ∧ (∀ j, j ≠ 0 → D p j = 0)
  exact ⟨by rw [hD, hs, mul_zero, add_zero, hBp],
    fun i hi => by rw [hD, hs, mul_zero, add_zero, hB₀ i hi],
    fun j hj => by
      have hj' : (0 : Fin (n + 1)) < j := Fin.pos_iff_ne_zero.mpr hj
      rw [hD, hBp, show s j = -(B p j / M p 0) from if_pos hj',
        mul_comm (M p 0), neg_mul, div_mul_cancel₀ _ hp, add_neg_cancel]⟩

end GlobalTheory.GLq
