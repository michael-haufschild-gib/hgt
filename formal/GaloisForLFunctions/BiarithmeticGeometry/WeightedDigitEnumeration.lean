import GaloisForLFunctions.BiarithmeticGeometry.WeightedDigitMoments
import GaloisForLFunctions.BiarithmeticGeometry.WeightedBaseFiveDigits
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination

/-!
# Natural-index enumeration of weighted digit words

The base-five word equivalence identifies its digits with Euclidean quotients and
remainders. It transports the complete signed moments to ordinary integer indices.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Read the first `M` base-five digits with arbitrary signed weights. -/
def fiveTruncatedDigitReadout (M : ℕ) (x : Fin M → ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin M, ((n / 5 ^ (i : ℕ) % 5 : ℕ) : ℝ) * x i

private theorem fiveWord_digit {M : ℕ} (d : Fin M → Fin 5) (i : Fin M) :
    (finFunctionFinEquiv d : ℕ) / 5 ^ (i : ℕ) % 5 = (d i : ℕ) := by
  have h := congrArg (fun e : Fin M → Fin 5 => (e i : ℕ))
    (finFunctionFinEquiv.symm_apply_apply d)
  exact h

/-- Reading the integer represented by a word recovers precisely its signed readout. -/
theorem fiveTruncatedDigitReadout_word {M : ℕ} (x : Fin M → ℝ) (d : Fin M → Fin 5) :
    fiveTruncatedDigitReadout M x (finFunctionFinEquiv d) = fiveDigitReadout x d := by
  unfold fiveTruncatedDigitReadout fiveDigitReadout
  apply sum_congr rfl
  intro i _
  rw [fiveWord_digit]

/-- The first moment over every integer below a base-five power. -/
theorem sum_fiveTruncatedDigitReadout (M : ℕ) (x : Fin M → ℝ) :
    (∑ n : Fin (5 ^ M), fiveTruncatedDigitReadout M x n) =
      (5 : ℝ) ^ M * (2 * ∑ i, x i) := by
  rw [← finFunctionFinEquiv.sum_comp (fun n : Fin (5 ^ M) =>
    fiveTruncatedDigitReadout M x n)]
  simp_rw [fiveTruncatedDigitReadout_word]
  exact sum_fiveDigitReadout M x

/-- The signed second moment over every integer below a base-five power. -/
theorem sum_sq_fiveTruncatedDigitReadout (M : ℕ) (x : Fin M → ℝ) :
    (∑ n : Fin (5 ^ M), fiveTruncatedDigitReadout M x n ^ 2) =
      (5 : ℝ) ^ M * (2 * ∑ i, x i ^ 2 + 4 * (∑ i, x i) ^ 2) := by
  rw [← finFunctionFinEquiv.sum_comp (fun n : Fin (5 ^ M) =>
    fiveTruncatedDigitReadout M x n ^ 2)]
  simp_rw [fiveTruncatedDigitReadout_word]
  exact sum_sq_fiveDigitReadout M x

theorem sum_sq_fiveTruncatedDigitReadout_range (M : ℕ) (x : Fin M → ℝ) :
    (∑ n ∈ range (5 ^ M), fiveTruncatedDigitReadout M x n ^ 2) =
      (5 : ℝ) ^ M * (2 * ∑ i, x i ^ 2 + 4 * (∑ i, x i) ^ 2) := by
  rw [← Fin.sum_univ_eq_sum_range
    (fun n : ℕ => fiveTruncatedDigitReadout M x n ^ 2) (5 ^ M)]
  exact sum_sq_fiveTruncatedDigitReadout M x

/-- Increasing the readout length appends exactly one leading-digit term. -/
theorem fiveTruncatedDigitReadout_succ (M : ℕ) (x : Fin (M + 1) → ℝ) (n : ℕ) :
    fiveTruncatedDigitReadout (M + 1) x n =
      fiveTruncatedDigitReadout M (fun i => x i.castSucc) n +
        ((n / 5 ^ M % 5 : ℕ) : ℝ) * x (Fin.last M) := by
  rw [fiveTruncatedDigitReadout, Fin.sum_univ_castSucc]
  rfl

/-- Removing the least significant digit shifts all remaining weights. -/
theorem fiveTruncatedDigitReadout_low_split (M : ℕ) (x : Fin (M + 1) → ℝ) (n : ℕ) :
    fiveTruncatedDigitReadout (M + 1) x n =
      (n % 5 : ℕ) * x 0 +
        fiveTruncatedDigitReadout M (fun i => x i.succ) (n / 5) := by
  rw [fiveTruncatedDigitReadout, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, Nat.div_one]
  congr 1
  apply sum_congr rfl
  intro i _
  simp only [Fin.val_succ, pow_succ', Nat.div_div_eq_div_mul]

/-- Geometric digit weights recover the original weighted base-five polynomial. -/
theorem fiveDigitRow_eq_truncated (a : ℝ) (M n : ℕ) (hn : n < 5 ^ M) :
    fiveDigitRow a n = fiveTruncatedDigitReadout M (fun i => a ^ (i : ℕ)) n := by
  induction M generalizing n with
  | zero =>
    have hn0 : n = 0 := by rw [pow_zero] at hn; omega
    subst n
    simp [fiveDigitRow_zero, fiveTruncatedDigitReadout]
  | succ M ih =>
    have hq : n / 5 < 5 ^ M := by rw [pow_succ] at hn; omega
    rw [fiveDigitRow_rec, ih _ hq, fiveTruncatedDigitReadout_low_split]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
    congr 1
    rw [fiveTruncatedDigitReadout, fiveTruncatedDigitReadout, mul_sum]
    apply sum_congr rfl
    intro i _
    rw [pow_succ]
    ring

/-- The full finite digit readout, with the exact natural logarithm selecting its length. -/
def fiveWeightedDigitRow (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  fiveTruncatedDigitReadout (Nat.log 5 n + 1) (fun i => x i) n

theorem fiveWeightedDigitRow_zero (x : ℕ → ℝ) : fiveWeightedDigitRow x 0 = 0 := by
  simp [fiveWeightedDigitRow, fiveTruncatedDigitReadout]

theorem fiveWeightedDigitRow_geometric (a : ℝ) (n : ℕ) :
    fiveWeightedDigitRow (fun i => a ^ i) n = fiveDigitRow a n := by
  exact (fiveDigitRow_eq_truncated a (Nat.log 5 n + 1) n
    (Nat.lt_pow_succ_log_self (by omega : 1 < 5) n)).symm

/-- A complete base-five block uses one fixed finite digit readout. -/
theorem fiveWeightedDigitRow_on_block (x : ℕ → ℝ) (M n : ℕ)
    (hlo : 5 ^ M ≤ n) (hhi : n < 5 ^ (M + 1)) :
    fiveWeightedDigitRow x n = fiveTruncatedDigitReadout (M + 1) (fun i => x i) n := by
  have hn : n ≠ 0 := by have hp : 0 < 5 ^ M := pow_pos (by omega) M; omega
  have hlog : Nat.log 5 n = M :=
    (Nat.log_eq_iff (Or.inr ⟨by omega, hn⟩)).mpr ⟨hlo, hhi⟩
  unfold fiveWeightedDigitRow
  rw [hlog]

/-- The actual annular integer moment, including every signed cross term. -/
theorem sum_sq_fiveWeightedDigitRow_block (x : ℕ → ℝ) (M : ℕ) :
    (∑ n ∈ Ico (5 ^ M) (5 ^ (M + 1)), fiveWeightedDigitRow x n ^ 2) =
      4 * (5 : ℝ) ^ M *
        ((5 / 4 : ℝ) * x M ^ 2 + 2 * ∑ i : Fin M, x i ^ 2 +
          ((5 / 2 : ℝ) * x M + 2 * ∑ i : Fin M, x i) ^ 2) := by
  have hlo :
      (∑ n ∈ range (5 ^ M),
        fiveTruncatedDigitReadout (M + 1) (fun i => x i) n ^ 2) =
      (5 : ℝ) ^ M * (2 * ∑ i : Fin M, x i ^ 2 + 4 * (∑ i : Fin M, x i) ^ 2) := by
    calc
      _ = ∑ n ∈ range (5 ^ M), fiveTruncatedDigitReadout M (fun i => x i) n ^ 2 := by
        apply sum_congr rfl
        intro n hn
        rw [fiveTruncatedDigitReadout_succ, Nat.div_eq_of_lt (mem_range.mp hn)]
        simp only [Nat.zero_mod, Nat.cast_zero, zero_mul, add_zero, Fin.val_castSucc]
      _ = _ := sum_sq_fiveTruncatedDigitReadout_range M (fun i => x i)
  have hcut := sum_range_add_sum_Ico
    (fun n => fiveTruncatedDigitReadout (M + 1) (fun i => x i) n ^ 2)
    (show 5 ^ M ≤ 5 ^ (M + 1) by rw [pow_succ]; omega)
  rw [hlo, sum_sq_fiveTruncatedDigitReadout_range] at hcut
  simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last] at hcut
  rw [pow_succ (5 : ℝ)] at hcut
  calc
    _ = ∑ n ∈ Ico (5 ^ M) (5 ^ (M + 1)),
        fiveTruncatedDigitReadout (M + 1) (fun i => x i) n ^ 2 := by
      apply sum_congr rfl
      intro n hn
      rw [fiveWeightedDigitRow_on_block x M n (mem_Ico.mp hn).1 (mem_Ico.mp hn).2]
    _ = _ := by linear_combination hcut

/-- The leading coefficient retains a positive variance on its complete integer block. -/
theorem fiveWeightedDigitRow_block_lower (x : ℕ → ℝ) (M : ℕ) :
    (5 : ℝ) ^ (M + 1) * x M ^ 2 ≤
      ∑ n ∈ Ico (5 ^ M) (5 ^ (M + 1)), fiveWeightedDigitRow x n ^ 2 := by
  rw [sum_sq_fiveWeightedDigitRow_block, pow_succ]
  have hx : 0 ≤ ∑ i : Fin M, x i ^ 2 := sum_nonneg fun i _ => sq_nonneg (x i)
  have hm : 0 ≤ ((5 / 2 : ℝ) * x M + 2 * ∑ i : Fin M, x i) ^ 2 := sq_nonneg _
  have hp : 0 ≤ (5 : ℝ) ^ M := pow_nonneg (by norm_num) M
  nlinarith only [mul_nonneg hp hx, mul_nonneg hp hm]

end GaloisForLFunctions.BiarithmeticGeometry
