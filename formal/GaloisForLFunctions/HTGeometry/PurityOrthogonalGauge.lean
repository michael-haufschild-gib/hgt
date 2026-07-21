import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Real.Basic

/-!
# Orthogonal gauge classification from a purity Gram law

Equality of the Euclidean purity kernels of two full square frames is equivalent to an
orthogonal change of frame.  This is the finite-dimensional algebraic classifier used by the
simplex Bernstein purity theorem.
-/

namespace HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A real square matrix is orthogonal when its columns have identity Gram matrix. -/
def IsOrthogonalGauge (O : Matrix n n ℝ) : Prop :=
  O.transpose * O = 1

/-- Multiplying a frame on the left by an orthogonal gauge preserves its column Gram matrix. -/
theorem transpose_mul_self_eq_of_orthogonal_mul
    {A B O : Matrix n n ℝ} (hO : IsOrthogonalGauge O) (hA : A = O * B) :
    A.transpose * A = B.transpose * B := by
  rw [hA, Matrix.transpose_mul]
  calc
    B.transpose * O.transpose * (O * B) =
        B.transpose * ((O.transpose * O) * B) := by
      simp only [Matrix.mul_assoc]
    _ = B.transpose * B := by rw [hO, Matrix.one_mul]

/-- **Purity orthogonal-gauge classification.**  Two full real square frames have the same
column Gram matrix exactly when one is a unique orthogonal left gauge of the other. -/
theorem gram_eq_iff_existsUnique_orthogonalGauge_mul
    (A B : Matrix n n ℝ) (hB : IsUnit B.det) :
    A.transpose * A = B.transpose * B ↔
      ∃! O : Matrix n n ℝ, IsOrthogonalGauge O ∧ A = O * B := by
  constructor
  · intro hGram
    let O : Matrix n n ℝ := A * B⁻¹
    have hBt : IsUnit B.transpose.det := by
      simpa using hB
    have hOrth : IsOrthogonalGauge O := by
      rw [IsOrthogonalGauge]
      dsimp only [O]
      rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
      calc
        B.transpose⁻¹ * A.transpose * (A * B⁻¹) =
            B.transpose⁻¹ * (A.transpose * A) * B⁻¹ := by
              simp only [Matrix.mul_assoc]
        _ = B.transpose⁻¹ * (B.transpose * B) * B⁻¹ := by rw [hGram]
        _ = (B.transpose⁻¹ * B.transpose) * (B * B⁻¹) := by
              simp only [Matrix.mul_assoc]
        _ = 1 := by
              rw [Matrix.nonsing_inv_mul _ hBt, Matrix.mul_nonsing_inv _ hB]
              simp
    have hMul : A = O * B := by
      dsimp only [O]
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB, Matrix.mul_one]
    refine ⟨O, ⟨hOrth, hMul⟩, ?_⟩
    intro P hP
    calc
      P = P * 1 := by simp
      _ = P * (B * B⁻¹) := by rw [Matrix.mul_nonsing_inv _ hB]
      _ = (P * B) * B⁻¹ := by rw [Matrix.mul_assoc]
      _ = A * B⁻¹ := by rw [← hP.2]
      _ = O := rfl
  · rintro ⟨O, ⟨hO, hA⟩, _huniq⟩
    exact transpose_mul_self_eq_of_orthogonal_mul hO hA

/-- The unique orthogonal gauge supplied by equal Gram matrices is explicitly `A * B⁻¹`. -/
theorem orthogonalGauge_eq_mul_nonsing_inv
    {A B O : Matrix n n ℝ} (hB : IsUnit B.det)
    (_hO : IsOrthogonalGauge O) (hA : A = O * B) :
    O = A * B⁻¹ := by
  calc
    O = O * 1 := by simp
    _ = O * (B * B⁻¹) := by rw [Matrix.mul_nonsing_inv _ hB]
    _ = (O * B) * B⁻¹ := by rw [Matrix.mul_assoc]
    _ = A * B⁻¹ := by rw [← hA]

/-- A lower-triangular real orthogonal matrix with positive diagonal is the identity.  The
index type may be any finite linear order; no choice of a `Fin` enumeration is part of the
statement. -/
theorem lowerTriangular_orthogonal_pos_diag_eq_one
    {i : Type*} [Fintype i] [DecidableEq i] [LinearOrder i]
    (U : Matrix i i ℝ)
    (htri : U.BlockTriangular (fun a : i => OrderDual.toDual a))
    (horth : U * U.transpose = 1)
    (hdiag : ∀ a, 0 < U a a) :
    U = 1 := by
  have hcol : ∀ a b : i, U b a = if b = a then 1 else 0 := by
    intro a
    induction a using WellFoundedLT.induction with
    | ind a ih =>
        intro b
        have hrowzero : ∀ k : i, k ≠ a → U a k = 0 := by
          intro k hka
          rcases lt_or_gt_of_ne hka with hlt | hgt
          · have hk := ih k hlt a
            simpa [Ne.symm hka] using hk
          · exact htri (by simpa using hgt)
        have haaEntry := congrFun (congrFun horth a) a
        simp only [Matrix.mul_apply, Matrix.one_apply, if_pos] at haaEntry
        have haaSq : U a a * U a a = 1 := by
          rw [Finset.sum_eq_single a] at haaEntry
          · simpa [Matrix.transpose_apply] using haaEntry
          · intro k hk hka
            rw [Matrix.transpose_apply, hrowzero k hka, mul_zero]
          · intro ha
            simp at ha
        have haa : U a a = 1 := by
          nlinarith [hdiag a]
        by_cases hba : b = a
        · subst b
          rw [haa, if_pos rfl]
        · rw [if_neg hba]
          rcases lt_or_gt_of_ne hba with hlt | hgt
          · exact htri (by simpa using hlt)
          · have hbaEntry := congrFun (congrFun horth b) a
            rw [Matrix.mul_apply, Matrix.one_apply, if_neg hba] at hbaEntry
            rw [Finset.sum_eq_single a] at hbaEntry
            · simpa [Matrix.transpose_apply, haa] using hbaEntry
            · intro k hk hka
              rw [Matrix.transpose_apply, hrowzero k hka, mul_zero]
            · intro ha
              simp at ha
  ext b a
  simpa [Matrix.one_apply] using hcol a b

/-- An upper-triangular real orthogonal matrix with positive diagonal is the identity. -/
theorem upperTriangular_orthogonal_pos_diag_eq_one
    {i : Type*} [Fintype i] [DecidableEq i] [LinearOrder i]
    (U : Matrix i i ℝ)
    (htri : U.BlockTriangular id)
    (horth : U.transpose * U = 1)
    (hdiag : ∀ a, 0 < U a a) :
    U = 1 := by
  have httri : U.transpose.BlockTriangular (fun a : i => OrderDual.toDual a) := by
    simpa using htri.transpose
  have htorth : U.transpose * U.transpose.transpose = 1 := by
    simpa using horth
  have htdiag : ∀ a, 0 < U.transpose a a := by
    simpa using hdiag
  have ht := lowerTriangular_orthogonal_pos_diag_eq_one U.transpose httri htorth htdiag
  exact Matrix.transpose_injective (by simpa using ht)

/-- The diagonal of a product of two upper-triangular matrices is the product of their
diagonals. -/
theorem upperTriangular_mul_apply_diag
    {i : Type*} [Fintype i] [DecidableEq i] [LinearOrder i]
    {A B : Matrix i i ℝ}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (a : i) :
    (A * B) a a = A a a * B a a := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single a
  · intro k hk hka
    rcases lt_or_gt_of_ne hka with hlt | hgt
    · rw [hA (by simpa using hlt), zero_mul]
    · rw [hB (by simpa using hgt), mul_zero]
  · intro ha
    simp at ha

/-- **Canonical purity-frame rigidity.**  Positive-diagonal upper-triangular real frames with
the same column Gram matrix are equal.  This is the orientation selector for the binomial
lower-set purity law. -/
theorem upperTriangular_pos_diag_eq_of_gram_eq
    {i : Type*} [Fintype i] [DecidableEq i] [LinearOrder i]
    (A B : Matrix i i ℝ)
    (hAtri : A.BlockTriangular id) (hBtri : B.BlockTriangular id)
    (hAdiag : ∀ a, 0 < A a a) (hBdiag : ∀ a, 0 < B a a)
    (hGram : A.transpose * A = B.transpose * B) :
    A = B := by
  have hBdet : IsUnit B.det := by
    rw [Matrix.det_of_upperTriangular hBtri]
    exact isUnit_iff_ne_zero.mpr
      (Finset.prod_ne_zero_iff.mpr fun a _ => ne_of_gt (hBdiag a))
  obtain ⟨O, ⟨hOorth, hA⟩, _huniq⟩ :=
    (gram_eq_iff_existsUnique_orthogonalGauge_mul A B hBdet).mp hGram
  letI : Invertible B := Matrix.invertibleOfIsUnitDet B hBdet
  have hBinvtri : B⁻¹.BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular hBtri
  have hOform : O = A * B⁻¹ :=
    orthogonalGauge_eq_mul_nonsing_inv hBdet hOorth hA
  have hOtri : O.BlockTriangular id := by
    rw [hOform]
    exact hAtri.mul hBinvtri
  have hOdiag : ∀ a, 0 < O a a := by
    intro a
    have hdiagEq : O a a * B a a = A a a := by
      rw [← upperTriangular_mul_apply_diag hOtri hBtri a, ← hA]
    nlinarith [hAdiag a, hBdiag a]
  have hO : O = 1 :=
    upperTriangular_orthogonal_pos_diag_eq_one O hOtri hOorth hOdiag
  simpa [hO] using hA

end

end HTGeometry
