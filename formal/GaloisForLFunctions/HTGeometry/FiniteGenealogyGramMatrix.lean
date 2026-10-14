import GaloisForLFunctions.HTGeometry.FinitePathContinuant
import Mathlib.Analysis.Complex.Norm

/-! # The positive continuant and exact coefficient recovery for scalar genealogies

The path matrix has diagonal `2, 2+|c₀|², ...` in oldest-first order.
Its positive determinant sequence recovers every squared certificate magnitude.
The full-operator identification is supplied by the subsequent genealogy modules.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped ComplexConjugate

def genealogyPathDiagonal (w : ℕ → ℂ) : ℕ → ℂ
  | 0 => 2
  | n + 1 => 2 + ((‖w n‖ ^ 2 : ℝ) : ℂ)

def genealogyPathMatrix (w : ℕ → ℂ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  finitePathMatrix (genealogyPathDiagonal w) (fun n => -conj (w n)) (fun n => -w n) N

def finiteGenealogyGramValue (w : ℕ → ℂ) : ℕ → ℝ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * finiteGenealogyGramValue w (n + 1) +
      ‖w n‖ ^ 2 * (finiteGenealogyGramValue w (n + 1) - finiteGenealogyGramValue w n)

@[simp] theorem finiteGenealogyGramValue_zero (w : ℕ → ℂ) : finiteGenealogyGramValue w 0 = 1 := rfl

@[simp] theorem finiteGenealogyGramValue_one (w : ℕ → ℂ) : finiteGenealogyGramValue w 1 = 2 := rfl

theorem finiteGenealogyGramValue_succ_succ (w : ℕ → ℂ) (N : ℕ) :
    finiteGenealogyGramValue w (N + 2) = 2 * finiteGenealogyGramValue w (N + 1) +
      ‖w N‖ ^ 2 * (finiteGenealogyGramValue w (N + 1) - finiteGenealogyGramValue w N) := rfl

theorem det_genealogyPathMatrix_succ_succ (w : ℕ → ℂ) (N : ℕ) :
    (genealogyPathMatrix w (N + 2)).det =
      (2 + ((‖w N‖ ^ 2 : ℝ) : ℂ)) * (genealogyPathMatrix w (N + 1)).det -
        ((‖w N‖ ^ 2 : ℝ) : ℂ) * (genealogyPathMatrix w N).det := by
  rw [genealogyPathMatrix, det_finitePathMatrix_succ_succ]
  simp only [genealogyPathDiagonal, neg_mul_neg]
  rw [mul_comm (conj (w N)) (w N), Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rfl

theorem det_genealogyPathMatrix (w : ℕ → ℂ) (N : ℕ) :
    (genealogyPathMatrix w N).det = (finiteGenealogyGramValue w N : ℂ) := by
  induction N using Nat.twoStepInduction with
  | zero => simp [genealogyPathMatrix]
  | one => simp [genealogyPathMatrix, genealogyPathDiagonal]
  | more N hN hN1 =>
      rw [det_genealogyPathMatrix_succ_succ, hN, hN1, finiteGenealogyGramValue_succ_succ]
      push_cast
      ring

private theorem positive_and_increasing (w : ℕ → ℂ) (N : ℕ) :
    0 < finiteGenealogyGramValue w N ∧
      finiteGenealogyGramValue w N < finiteGenealogyGramValue w (N + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      refine ⟨lt_trans ih.1 ih.2, ?_⟩
      rw [finiteGenealogyGramValue_succ_succ]
      have h := mul_nonneg (sq_nonneg ‖w N‖) (sub_nonneg.mpr ih.2.le)
      linarith

theorem finiteGenealogyGramValue_pos (w : ℕ → ℂ) (N : ℕ) :
    0 < finiteGenealogyGramValue w N := (positive_and_increasing w N).1

theorem finiteGenealogyGramValue_lt_succ (w : ℕ → ℂ) (N : ℕ) :
    finiteGenealogyGramValue w N < finiteGenealogyGramValue w (N + 1) :=
  (positive_and_increasing w N).2

theorem finiteGenealogyGramValue_increment_pos (w : ℕ → ℂ) (N : ℕ) :
    0 < finiteGenealogyGramValue w (N + 1) - finiteGenealogyGramValue w N :=
  sub_pos.mpr (finiteGenealogyGramValue_lt_succ w N)

theorem finiteGenealogyGramValue_two_mul_le_succ (w : ℕ → ℂ) (N : ℕ) :
    2 * finiteGenealogyGramValue w N ≤ finiteGenealogyGramValue w (N + 1) := by
  cases N with
  | zero => norm_num
  | succ N =>
      rw [finiteGenealogyGramValue_succ_succ]
      exact le_add_of_nonneg_right
        (mul_nonneg (sq_nonneg _) (finiteGenealogyGramValue_increment_pos w N).le)

theorem two_pow_le_finiteGenealogyGramValue (w : ℕ → ℂ) (N : ℕ) :
    (2 : ℝ) ^ N ≤ finiteGenealogyGramValue w N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [pow_succ, mul_comm]
      exact (mul_le_mul_of_nonneg_left ih (by norm_num)).trans
        (finiteGenealogyGramValue_two_mul_le_succ w N)

theorem finiteGenealogyGramValue_recovers_norm_sq (w : ℕ → ℂ) (N : ℕ) :
    ‖w N‖ ^ 2 =
      (finiteGenealogyGramValue w (N + 2) - 2 * finiteGenealogyGramValue w (N + 1)) /
        (finiteGenealogyGramValue w (N + 1) - finiteGenealogyGramValue w N) := by
  apply (eq_div_iff (ne_of_gt (finiteGenealogyGramValue_increment_pos w N))).2
  rw [finiteGenealogyGramValue_succ_succ]
  ring

theorem finiteGenealogyGramValue_eq_iff (w v : ℕ → ℂ) :
    (∀ N, finiteGenealogyGramValue w N = finiteGenealogyGramValue v N) ↔
      ∀ n, ‖w n‖ = ‖v n‖ := by
  constructor
  · intro h n
    have hs : ‖w n‖ ^ 2 = ‖v n‖ ^ 2 := by
      rw [finiteGenealogyGramValue_recovers_norm_sq, finiteGenealogyGramValue_recovers_norm_sq,
        h n, h (n + 1), h (n + 2)]
    nlinarith [norm_nonneg (w n), norm_nonneg (v n)]
  · intro h N
    induction N using Nat.twoStepInduction with
    | zero => rfl
    | one => rfl
    | more N hN hN1 =>
        rw [finiteGenealogyGramValue_succ_succ, finiteGenealogyGramValue_succ_succ,
          hN, hN1, h N]

end
end GaloisForLFunctions.HTGeometry
