import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParabolicBlockMatrices

/-! Column translations and the corresponding first-column factorization
of an upper block matrix with identity leading block. -/

noncomputable section
open scoped Classical

namespace GlobalTheory.GLq

variable {g a b : ℕ} [Fact g.Prime]

local notation "Col" => (Fin a → ZMod g)
local notation "Rect" => Matrix (Fin a) (Fin (b + 1)) (ZMod g)

/-- Put a column vector in the first column of the upper-right rectangle. -/
def columnRectangle (v : Col) : Rect :=
  fun i j => if j = 0 then v i else 0

/-- The first column of the upper-right block gives a translation subgroup. -/
def columnTranslation (g a b : ℕ) [Fact g.Prime] :
    Multiplicative (Fin a → ZMod g) →* Gn g (a + (b + 1)) where
  toFun x := upperBlockUnit 1 (columnRectangle x.toAdd) 1
  map_one' := by
    have h : columnRectangle (b := b) (0 : Fin a → ZMod g) = 0 := by
      ext i j
      simp [columnRectangle]
    change upperBlockUnit 1 (columnRectangle (b := b) (0 : Fin a → ZMod g)) 1 = 1
    rw [h, upperBlockUnit_one]
  map_mul' x y := by
    change upperBlockUnit 1 (columnRectangle (x.toAdd + y.toAdd)) 1 =
      upperBlockUnit 1 (columnRectangle x.toAdd) 1 * upperBlockUnit 1 (columnRectangle y.toAdd) 1
    simp only [upperBlockUnit_mul, one_mul, Units.val_one, Matrix.one_mul, Matrix.mul_one]
    congr 1
    ext i j
    by_cases hj : j = 0 <;> simp [columnRectangle, hj, add_comm]

private theorem columnRectangle_mul_apply (v : Col) (D : Mt g (b + 1)) (i : Fin a) (j : Fin (b + 1)) :
    (columnRectangle (b := b) v * D : Rect) i j = v i * D 0 j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem 0 (Finset.mem_univ 0)]
  · rw [show columnRectangle (b := b) v i 0 = v i from if_pos rfl]
  · intro k _ hk
    rw [show columnRectangle (b := b) v i k = 0 from if_neg hk, zero_mul]

/-- Clearing the first column factors off its column translation. -/
theorem factor_first_column (X : Rect) (D : Gn g (b + 1))
    (hD : D.val 0 0 = 1) :
    ∃ Y : Rect, (∀ i, Y i 0 = 0) ∧
      upperBlockUnit 1 X D =
        columnTranslation g a b (Multiplicative.ofAdd (fun i => X i 0)) * upperBlockUnit 1 Y D := by
  let v : Col := fun i => X i 0
  refine ⟨X - columnRectangle v * D.val, fun i => ?_, ?_⟩
  · change X i 0 - (columnRectangle (b := b) v * D.val : Rect) i 0 = 0
    rw [columnRectangle_mul_apply, hD, mul_one, sub_self]
  · change upperBlockUnit 1 X D = upperBlockUnit 1 (columnRectangle v) 1 *
      upperBlockUnit 1 (X - columnRectangle v * D.val) D
    simp only [upperBlockUnit_mul, one_mul, Units.val_one, Matrix.one_mul]
    exact congrArg (fun Y : Rect => upperBlockUnit 1 Y D)
      (sub_add_cancel X (columnRectangle (b := b) v * D.val)).symm

/-- Conjugating a matrix with zero first rectangle column by a column translation
preserves its diagonal blocks and its zero first rectangle column. -/
theorem move_columnTranslation_left (v : Col) (X : Rect) (D : Gn g (b + 1))
    (hD : D.val 0 0 = 1) (hX : ∀ i, X i 0 = 0) :
    ∃ Y : Rect, (∀ i, Y i 0 = 0) ∧
      upperBlockUnit 1 X D * columnTranslation g a b (Multiplicative.ofAdd v) =
        columnTranslation g a b (Multiplicative.ofAdd v) * upperBlockUnit 1 Y D := by
  refine ⟨X + columnRectangle v - columnRectangle v * D.val, fun i => ?_, ?_⟩
  · change X i 0 + columnRectangle (b := b) v i 0 - (columnRectangle (b := b) v * D.val : Rect) i 0 = 0
    rw [hX, columnRectangle_mul_apply, hD, mul_one, zero_add]
    exact sub_self (v i)
  · change upperBlockUnit 1 X D * upperBlockUnit 1 (columnRectangle v) 1 =
      upperBlockUnit 1 (columnRectangle v) 1 *
        upperBlockUnit 1 (X + columnRectangle v - columnRectangle v * D.val) D
    simp only [upperBlockUnit_mul, one_mul, mul_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
    exact congrArg (fun Y : Rect => upperBlockUnit 1 Y D)
      ((add_comm (columnRectangle (b := b) v) X).trans
        (sub_add_cancel (X + columnRectangle (b := b) v) (columnRectangle (b := b) v * D.val)).symm)

/-- The first diagonal block acts on the rectangle by left matrix multiplication. -/
theorem move_diagonal_right (A : Gn g a) (X : Rect) (D : Gn g (b + 1)) :
    upperBlockUnit A 0 1 * upperBlockUnit 1 X D =
      upperBlockUnit 1 (A.val * X) D * upperBlockUnit A 0 1 := by
  simp only [upperBlockUnit_mul, one_mul, mul_one, Units.val_one, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.mul_one, zero_add, add_zero]

/-- Conjugating a column translation by the leading diagonal block acts
on the column through the defining matrix representation. -/
theorem move_diagonal_column (A : Gn g a) (v : Col) :
    upperBlockUnit A (0 : Rect) 1 * columnTranslation g a b (Multiplicative.ofAdd v) =
      columnTranslation g a b (Multiplicative.ofAdd (A.val.mulVec v)) * upperBlockUnit A (0 : Rect) 1 := by
  have he : A.val * columnRectangle (b := b) v = columnRectangle (A.val.mulVec v) := by
    ext i j
    by_cases h : j = 0
    · subst j
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, columnRectangle]
    · simp [Matrix.mul_apply, columnRectangle, h]
  change upperBlockUnit A (0 : Rect) 1 * upperBlockUnit 1 (columnRectangle v) 1 =
    upperBlockUnit 1 (columnRectangle (A.val.mulVec v)) 1 * upperBlockUnit A (0 : Rect) 1
  exact (move_diagonal_right A (columnRectangle v) 1).trans
    (congrArg (fun X => upperBlockUnit 1 X 1 * upperBlockUnit A (0 : Rect) 1) he)

end GlobalTheory.GLq
