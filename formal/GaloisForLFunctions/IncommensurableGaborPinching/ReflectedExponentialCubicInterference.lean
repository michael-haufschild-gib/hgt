import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# Cubic interference of reflected exponential evaluations

Exponential evaluations on `[-1,1]` have overlap `sinh z / z`, with its removable
value one at zero. Two reflected pairs produce a signed Gram matrix whose cubic
trace retains cross-height interference.
-/

open Complex Matrix Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.IncommensurableGaborPinching

/-- The normalized overlap of two exponential evaluations. -/
def exponentialOverlap (z : ℂ) : ℂ := if z = 0 then 1 else Complex.sinh z / z

/-- The overlap is the actual integral on the interval with measure `du/2`. -/
theorem exponentialOverlap_eq_integral (z : ℂ) :
    exponentialOverlap z = (∫ u : ℝ in -1..1, Complex.exp (z * u)) / 2 := by
  by_cases hz : z = 0
  · subst z
    norm_num [exponentialOverlap]
  · rw [exponentialOverlap, if_neg hz, integral_exp_mul_complex hz, Complex.sinh]
    norm_num
    ring

@[simp] theorem exponentialOverlap_zero : exponentialOverlap 0 = 1 := by
  simp [exponentialOverlap]

@[simp] theorem exponentialOverlap_neg (z : ℂ) : exponentialOverlap (-z) = exponentialOverlap z := by
  by_cases hz : z = 0
  · simp [hz]
  · simp [exponentialOverlap, hz, Complex.sinh_neg]

@[simp] theorem exponentialOverlap_conj (z : ℂ) :
    exponentialOverlap (conj z) = conj (exponentialOverlap z) := by
  by_cases hz : z = 0
  · simp [hz]
  · simp [exponentialOverlap, hz, Complex.sinh_conj]

/-- The overlap formula retains the literal exponential evaluation vectors. -/
theorem exponentialOverlap_eq_evaluation_inner (z w : ℂ) :
    exponentialOverlap (conj z + w) =
      (∫ u : ℝ in -1..1, conj (Complex.exp (z * u)) * Complex.exp (w * u)) / 2 := by
  rw [exponentialOverlap_eq_integral]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  rw [add_mul, Complex.exp_add, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal]

/-- Gram pattern of two reflected pairs, with real diagonal and height overlaps. -/
def reflectedEvaluationGram (g h : ℝ) (f : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![g, 1, conj f, h;
     1, g, h, f;
     f, h, g, 1;
     h, conj f, 1, g]

/-- Reflection exchanges the two members of each pair. -/
def reflectedPairSwap : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

private theorem reflectedPairSwap_mul_gram (g h : ℝ) (f : ℂ) :
    reflectedPairSwap * reflectedEvaluationGram g h f =
      !![1, g, h, f; g, 1, conj f, h; h, conj f, 1, g; f, h, g, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reflectedPairSwap, reflectedEvaluationGram, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Exact cubic trace: cross-height interference survives reflection symmetry. -/
theorem reflectedEvaluation_cubic_trace (g h : ℝ) (f : ℂ) :
    (((reflectedPairSwap * reflectedEvaluationGram g h f) ^ 3).trace).re =
      4 + 12 * (g ^ 2 + h ^ 2 + (f ^ 2).re + 2 * g * h * f.re) := by
  rw [reflectedPairSwap_mul_gram]
  norm_num [Matrix.trace, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ,
    Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

end GaloisForLFunctions.IncommensurableGaborPinching
