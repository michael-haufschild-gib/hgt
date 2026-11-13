import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Complementary compressions do not determine singleton runs

A six-dimensional balanced projection and a diagonal phase exchange the two
compressed halves while preserving the source. An exact mixture matches the
second and fourth compressed moments with only four singleton coordinates.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.IncommensurableGaborPinching

/-- A balanced projection whose first two coordinates couple to two auxiliary
coordinates; the last two coordinates supply its third rank. -/
def splitBandProjection (r c : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1/2, c, r, 0, 0, 0;
     c, 1/2, 0, r, 0, 0;
     r, 0, 1/2, -c, 0, 0;
     0, r, -c, 1/2, 0, 0;
     0, 0, 0, 0, 1/2, 1/2;
     0, 0, 0, 0, 1/2, 1/2]

def splitBandPhase : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.diagonal ![1, -1, -1, 1, 1, -1]

def splitBandSource : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.diagonal ![-1, 1, 0, 0, 0, 0]

theorem splitBandProjection_isHermitian (r c : ℝ) :
    (splitBandProjection r c).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [splitBandProjection, Matrix.conjTranspose_apply]

theorem splitBandProjection_sq {r c : ℝ} (h : r ^ 2 + c ^ 2 = 1/4) :
    splitBandProjection r c * splitBandProjection r c = splitBandProjection r c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [splitBandProjection, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    nlinarith only [h]

theorem splitBandProjection_trace (r c : ℝ) :
    (splitBandProjection r c).trace = 3 := by
  norm_num [Matrix.trace, splitBandProjection, Fin.sum_univ_succ]

theorem splitBandPhase_sq : splitBandPhase * splitBandPhase = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [splitBandPhase, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal_apply]

theorem splitBandPhase_exchanges_halves (r c : ℝ) :
    splitBandPhase * splitBandProjection r c * splitBandPhase = 1 - splitBandProjection r c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [splitBandPhase, splitBandProjection, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.diagonal_apply]

theorem splitBandPhase_commutes_source :
    splitBandPhase * splitBandSource = splitBandSource * splitBandPhase := by
  rw [splitBandPhase, splitBandSource, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

/-- Only the first two rows survive multiplication by the source. -/
private theorem source_projection_sq (r c : ℝ) :
    (splitBandSource * splitBandProjection r c) ^ 2 =
      !![1/4-c^2, 0, r/2, -c*r, 0, 0;
         0, 1/4-c^2, -c*r, r/2, 0, 0;
         0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, splitBandSource, splitBandProjection, Matrix.mul_apply,
      Matrix.diagonal_apply, Fin.sum_univ_succ] <;> ring

theorem splitBandCompressed_second (r c : ℝ) :
    ((splitBandSource * splitBandProjection r c) ^ 2).trace = 2 * (1/4-c^2) := by
  rw [source_projection_sq]
  norm_num [Matrix.trace, Fin.sum_univ_succ]
  ring

theorem splitBandCompressed_third (r c : ℝ) :
    ((splitBandSource * splitBandProjection r c) ^ 3).trace = 0 := by
  have hd (i : Fin 6) : ((splitBandSource * splitBandProjection r c) ^ 3) i i =
      ![-(1/4-c^2)/2, (1/4-c^2)/2, 0, 0, 0, 0] i := by
    rw [pow_succ, source_projection_sq]
    fin_cases i <;>
      norm_num [splitBandSource, splitBandProjection, Matrix.mul_apply,
        Matrix.diagonal_apply, Fin.sum_univ_succ] <;> ring
  change (∑ i, ((splitBandSource * splitBandProjection r c) ^ 3) i i) = 0
  simp_rw [hd]
  norm_num [Fin.sum_univ_succ]
  ring

theorem splitBandCompressed_fourth (r c : ℝ) :
    ((splitBandSource * splitBandProjection r c) ^ 4).trace = 2 * (1/4-c^2)^2 := by
  rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, source_projection_sq]
  norm_num [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

theorem splitBandSource_second : (splitBandSource ^ 2).trace = 2 := by
  norm_num [splitBandSource, Matrix.trace, Matrix.diagonal_pow, Fin.sum_univ_succ]

theorem splitBandSource_fourth : (splitBandSource ^ 4).trace = 2 := by
  norm_num [splitBandSource, Matrix.trace, Matrix.diagonal_pow, Fin.sum_univ_succ]

/-- The two projection parameters in the exact moment mixture. -/
theorem splitBandProjection_parameters :
    (Real.sqrt (1/5)) ^ 2 + (Real.sqrt (1/20)) ^ 2 = (1:ℝ)/4 ∧
      (0:ℝ)^2 + (1/2)^2 = (1:ℝ)/4 := by
  rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
  norm_num

/-- The two equally sized compressed halves match the second and fourth target
moments even though the full source has only four singleton coordinates. -/
theorem splitBand_mixture_second_fourth :
    (5/8:ℝ) * (((splitBandSource * splitBandProjection (Real.sqrt (1/5))
      (Real.sqrt (1/20))) ^ 2).trace / 3) +
      (3/8:ℝ) * (((splitBandSource * splitBandProjection 0 (1/2)) ^ 2).trace / 3) = 1/12 ∧
    (5/8:ℝ) * (((splitBandSource * splitBandProjection (Real.sqrt (1/5))
      (Real.sqrt (1/20))) ^ 4).trace / 3) +
      (3/8:ℝ) * (((splitBandSource * splitBandProjection 0 (1/2)) ^ 4).trace / 3) = 1/60 := by
  rw [splitBandCompressed_second, splitBandCompressed_second,
    splitBandCompressed_fourth, splitBandCompressed_fourth,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/20)]
  norm_num

/-- Cyclicity identifies the power traces of two orders of a product. -/
private theorem trace_mul_pow_comm (A B : Matrix (Fin 6) (Fin 6) ℝ) (n : ℕ) :
    ((A * B) ^ n).trace = ((B * A) ^ n).trace := by
  have hpush (k : ℕ) : (A * B) ^ k * A = A * (B * A) ^ k := by
    induction k with
    | zero => simp only [pow_zero, one_mul, mul_one]
    | succ k hk =>
      rw [pow_succ, pow_succ]
      simpa only [mul_assoc] using congrArg (fun M => M * (B * A)) hk
  cases n with
  | zero => rfl
  | succ n =>
    rw [pow_succ, ← mul_assoc, hpush, Matrix.trace_mul_cycle, ← pow_succ']

/-- The displayed moments are moments of the Hermitian compressed source. -/
theorem splitBandCompression_trace_pow {r c : ℝ} (h : r ^ 2 + c ^ 2 = 1/4)
    (n : ℕ) :
    ((splitBandProjection r c * splitBandSource * splitBandProjection r c) ^ n).trace =
      ((splitBandSource * splitBandProjection r c) ^ n).trace := by
  rw [mul_assoc, trace_mul_pow_comm, mul_assoc, splitBandProjection_sq h]

/-- The full positive source has exactly four diagonal entries equal to one. -/
theorem splitBandSource_singleton_coordinates :
    (Finset.univ.filter fun i : Fin 6 => (1 + splitBandSource) i i = 1).card = 4 := by
  have hs : (Finset.univ.filter fun i : Fin 6 => (1 + splitBandSource) i i = 1) =
      {2, 3, 4, 5} := by
    ext i
    fin_cases i <;> norm_num [splitBandSource, Matrix.add_apply,
      Matrix.one_apply, Matrix.diagonal_apply] <;> decide
  rw [hs]
  decide

private theorem phase_conj_mul (A B : Matrix (Fin 6) (Fin 6) ℝ) :
    (splitBandPhase * A * splitBandPhase) * (splitBandPhase * B * splitBandPhase) =
      splitBandPhase * (A * B) * splitBandPhase := by
  calc
    _ = splitBandPhase * A * (splitBandPhase * splitBandPhase) * B * splitBandPhase := by
      simp only [mul_assoc]
    _ = _ := by rw [splitBandPhase_sq]; simp only [mul_one, mul_assoc]

private theorem phase_conj_pow (A : Matrix (Fin 6) (Fin 6) ℝ) (n : ℕ) :
    (splitBandPhase * A * splitBandPhase) ^ n =
      splitBandPhase * A ^ n * splitBandPhase := by
  induction n with
  | zero => simp only [pow_zero, mul_one, splitBandPhase_sq]
  | succ n hn => rw [pow_succ, hn, phase_conj_mul, ← pow_succ]

/-- Complementary halves have identical compressed power traces. -/
theorem splitBand_complementary_trace_pow (r c : ℝ) (n : ℕ) :
    (((1 - splitBandProjection r c) * splitBandSource *
      (1 - splitBandProjection r c)) ^ n).trace =
    ((splitBandProjection r c * splitBandSource * splitBandProjection r c) ^ n).trace := by
  have hH : splitBandPhase * splitBandSource * splitBandPhase = splitBandSource := by
    rw [splitBandPhase_commutes_source, mul_assoc, splitBandPhase_sq, mul_one]
  have hc : (1 - splitBandProjection r c) * splitBandSource * (1 - splitBandProjection r c) =
      splitBandPhase * (splitBandProjection r c * splitBandSource * splitBandProjection r c) *
        splitBandPhase := by
    rw [← splitBandPhase_exchanges_halves r c]
    nth_rw 1 [← hH]
    rw [phase_conj_mul, phase_conj_mul]
  rw [hc, phase_conj_pow, Matrix.trace_mul_cycle, splitBandPhase_sq, one_mul]

end GaloisForLFunctions.IncommensurableGaborPinching

#print axioms GaloisForLFunctions.IncommensurableGaborPinching.splitBand_mixture_second_fourth
#print axioms GaloisForLFunctions.IncommensurableGaborPinching.splitBandCompression_trace_pow
