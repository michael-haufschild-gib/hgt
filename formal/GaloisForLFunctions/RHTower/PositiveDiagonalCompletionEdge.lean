import Mathlib.Analysis.Matrix.PosDef

open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- Any positive diagonal completion of a Hermitian zero-diagonal edge pays the sharp `2 x 2`
principal-minor cost. -/
theorem positiveDiagonalCompletion_edge_bounds
    {n : Type*} [Fintype n] [DecidableEq n]
    (W : Matrix n n ℂ) (d : n → ℝ) (hW : W.IsHermitian)
    (a b : n) (hab : a ≠ b) (hWaa : W a a = 0) (hWbb : W b b = 0)
    (hpsd : (W + Matrix.diagonal (fun i => (d i : ℂ))).PosSemidef) :
    0 ≤ d a ∧ 0 ≤ d b ∧ ‖W a b‖ ^ 2 ≤ d a * d b := by
  let A := W + Matrix.diagonal (fun i => (d i : ℂ))
  have haC : (0 : ℂ) ≤ (d a : ℂ) := by
    simpa [A, Matrix.diagonal_apply, hWaa] using hpsd.diag_nonneg (i := a)
  have hbC : (0 : ℂ) ≤ (d b : ℂ) := by
    simpa [A, Matrix.diagonal_apply, hWbb] using hpsd.diag_nonneg (i := b)
  have ha : 0 ≤ d a := (Complex.nonneg_iff.mp haC).1
  have hb : 0 ≤ d b := (Complex.nonneg_iff.mp hbC).1
  have hWba : W b a = star (W a b) := by
    have h := congrArg star (hW.apply a b)
    simpa using h
  let e : Fin 2 → n := ![a, b]
  have hdet := (hpsd.submatrix e).det_nonneg
  rw [Matrix.det_fin_two] at hdet
  have hdetReal : (0 : ℝ) ≤ d a * d b - Complex.normSq (W a b) := by
    have hdetC : (0 : ℂ) ≤ ((d a * d b - Complex.normSq (W a b) : ℝ) : ℂ) := by
      simpa [e, A, Matrix.diagonal_apply, hab, Ne.symm hab, hWaa, hWbb, hWba,
        Complex.mul_conj] using hdet
    exact (Complex.nonneg_iff.mp hdetC).1
  refine ⟨ha, hb, ?_⟩
  rw [← Complex.normSq_eq_norm_sq]
  linarith

/-- A nonzero zero-diagonal edge forces both correcting diagonal entries to be strictly positive. -/
theorem positiveDiagonalCompletion_edge_strict
    {n : Type*} [Fintype n] [DecidableEq n]
    (W : Matrix n n ℂ) (d : n → ℝ) (hW : W.IsHermitian)
    (a b : n) (hab : a ≠ b) (hWaa : W a a = 0) (hWbb : W b b = 0)
    (hWab : W a b ≠ 0)
    (hpsd : (W + Matrix.diagonal (fun i => (d i : ℂ))).PosSemidef) :
    0 < d a ∧ 0 < d b := by
  obtain ⟨ha, hb, habBound⟩ :=
    positiveDiagonalCompletion_edge_bounds W d hW a b hab hWaa hWbb hpsd
  have hnorm : 0 < ‖W a b‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hWab)
  have hprod : 0 < d a * d b := hnorm.trans_le habBound
  constructor
  · by_contra hda
    have hzero : d a = 0 := le_antisymm (le_of_not_gt hda) ha
    rw [hzero, zero_mul] at hprod
    exact (lt_irrefl 0) hprod
  · by_contra hdb
    have hzero : d b = 0 := le_antisymm (le_of_not_gt hdb) hb
    rw [hzero, mul_zero] at hprod
    exact (lt_irrefl 0) hprod

end

end RHTower
