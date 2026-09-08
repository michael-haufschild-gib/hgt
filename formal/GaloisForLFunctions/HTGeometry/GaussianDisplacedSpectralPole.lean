import GaloisForLFunctions.HTGeometry.GaussianRealMoments
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gaussian displacement of spectral poles

Equations (20)--(21) of Nery--Longo--Verstraete, arXiv:2608.26494,
using the existing Gaussian moment recursion. The exact mean, variance,
and cubic centered moment are Bochner integrals. The special-displacement
comparison identifies the entire missing quadratic-coupling variance.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry


theorem integrable_gaussianMonomial (v : ℝ≥0) (c : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => c * x ^ n) (gaussianReal 0 v) :=
  (integrable_pow_of_mem_interior_integrableExpSet
    (X := fun x : ℝ => x) (μ := gaussianReal 0 v) (by simp) n).const_mul c

/-- Exact integration of any finite polynomial in a centered Gaussian displacement. -/
theorem integral_gaussianFinitePolynomial (v : ℝ≥0) {n : ℕ} (c : Fin n → ℝ) :
    (∫ x : ℝ, ∑ i, c i * x ^ i.val ∂gaussianReal 0 v) =
      ∑ i, c i * ∫ x : ℝ, x ^ i.val ∂gaussianReal 0 v := by
  rw [integral_finsetSum _ (fun i _ => integrable_gaussianMonomial v (c i) i.val)]
  simp only [integral_const_mul]

/-- The second through sixth Gaussian moments supplied by the corpus recursion. -/
theorem gaussianMoments_two_through_six (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = (v : ℝ) ∧
    (∫ x : ℝ, x ^ 3 ∂gaussianReal 0 v) = 0 ∧
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 ∧
    (∫ x : ℝ, x ^ 5 ∂gaussianReal 0 v) = 0 ∧
    (∫ x : ℝ, x ^ 6 ∂gaussianReal 0 v) = 15 * (v : ℝ) ^ 3 := by
  have h2 := integral_pow_gaussianReal_succ_succ v 0
  have h3 := integral_pow_gaussianReal_succ_succ v 1
  have h4 := integral_pow_gaussianReal_succ_succ v 2
  have h5 := integral_pow_gaussianReal_succ_succ v 3
  have h6 := integral_pow_gaussianReal_succ_succ v 4
  simp only [Nat.reduceAdd, integral_pow_zero_gaussianReal, integral_pow_one_gaussianReal,
    Nat.cast_ofNat, Nat.cast_zero, zero_add, mul_one, mul_zero] at h2 h3 h4 h5 h6
  refine ⟨by simpa using h2, by simpa using h3, ?_, ?_, ?_⟩
  · rw [h4, h2]; ring
  · rw [h5, h3]; ring
  · rw [h6, h4, h2]; ring

/-- Linear plus quadratic displacement of a spectral pole; `b` is half the second-order coupling. -/
def gaussianPolePosition (e g b x : ℝ) : ℝ := e + g * x + b * x ^ 2

/-- Debye--Waller shift from equation (21) of arXiv:2608.26494. -/
theorem integral_gaussianPolePosition (v : ℝ≥0) (e g b : ℝ) :
    (∫ x, gaussianPolePosition e g b x ∂gaussianReal 0 v) = e + b * v := by
  have h := integral_gaussianFinitePolynomial v (![e, g, b] : Fin 3 → ℝ)
  have hp : (fun x => gaussianPolePosition e g b x) =
      (fun x => ∑ i : Fin 3, (![e, g, b] : Fin 3 → ℝ) i * x ^ i.val) := by
    funext x
    simp [Fin.sum_univ_succ, gaussianPolePosition, add_assoc]
  rw [hp, h]
  simp [Fin.sum_univ_succ, (gaussianMoments_two_through_six v).1,
    integral_id_gaussianReal]

/-- Exact spectral variance, including the quadratic coupling's additional broadening. -/
theorem gaussianPolePosition_centered_second (v : ℝ≥0) (e g b : ℝ) :
    (∫ x, (gaussianPolePosition e g b x - (e + b * v)) ^ 2 ∂gaussianReal 0 v) =
      g ^ 2 * v + 2 * b ^ 2 * (v : ℝ) ^ 2 := by
  let c : Fin 5 → ℝ :=
    ![b ^ 2 * (v : ℝ) ^ 2, -2 * b * g * v,
      g ^ 2 - 2 * b ^ 2 * v, 2 * b * g, b ^ 2]
  have hp : (fun x => (gaussianPolePosition e g b x - (e + b * v)) ^ 2) =
      (fun x => ∑ i : Fin 5, c i * x ^ i.val) := by
    funext x
    simp only [c, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero, add_zero, pow_zero,
      gaussianPolePosition]
    ring
  rw [hp, integral_gaussianFinitePolynomial]
  rcases gaussianMoments_two_through_six v with ⟨h2, h3, h4, _, _⟩
  simp [c, Fin.sum_univ_succ, h2, h3, h4, integral_id_gaussianReal]
  ring

/-- The cubic centered moment gives an exact asymmetry law beyond the paper's mean and width. -/
theorem gaussianPolePosition_centered_third (v : ℝ≥0) (e g b : ℝ) :
    (∫ x, (gaussianPolePosition e g b x - (e + b * v)) ^ 3 ∂gaussianReal 0 v) =
      6 * b * g ^ 2 * (v : ℝ) ^ 2 + 8 * b ^ 3 * (v : ℝ) ^ 3 := by
  let c : Fin 7 → ℝ :=
    ![-b ^ 3 * (v : ℝ) ^ 3, 3 * b ^ 2 * g * (v : ℝ) ^ 2,
      3 * b ^ 3 * (v : ℝ) ^ 2 - 3 * b * g ^ 2 * v,
      g ^ 3 - 6 * b ^ 2 * g * v, 3 * b * g ^ 2 - 3 * b ^ 3 * v,
      3 * b ^ 2 * g, b ^ 3]
  have hp : (fun x => (gaussianPolePosition e g b x - (e + b * v)) ^ 3) =
      (fun x => ∑ i : Fin 7, c i * x ^ i.val) := by
    funext x
    simp only [c, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero, add_zero, pow_zero,
      gaussianPolePosition]
    ring
  rw [hp, integral_gaussianFinitePolynomial]
  rcases gaussianMoments_two_through_six v with ⟨h2, h3, h4, h5, h6⟩
  simp [c, Fin.sum_univ_succ, h2, h3, h4, h5, h6, integral_id_gaussianReal]
  ring

/-- The paper's spectral linewidth squared is an actual probabilistic variance. -/
theorem variance_gaussianPolePosition (v : ℝ≥0) (e g b : ℝ) :
    Var[gaussianPolePosition e g b; gaussianReal 0 v] =
      g ^ 2 * v + 2 * b ^ 2 * (v : ℝ) ^ 2 := by
  rw [variance_eq_integral (show AEMeasurable (gaussianPolePosition e g b)
    (gaussianReal 0 v) from (by unfold gaussianPolePosition; fun_prop)),
    integral_gaussianPolePosition, gaussianPolePosition_centered_second]

/-- Quadratic displacement coupling always increases variance above the linear Fan term. -/
theorem gaussianPole_variance_ge_linear (v : ℝ≥0) (e g b : ℝ) :
    g ^ 2 * v ≤ Var[gaussianPolePosition e g b; gaussianReal 0 v] := by
  rw [variance_gaussianPolePosition]
  exact le_add_of_nonneg_right (by positivity)

/-- The sign of cubic asymmetry follows the sign of the quadratic coupling. -/
theorem gaussianPole_quadraticCoupling_mul_third_nonneg (v : ℝ≥0) (e g b : ℝ) :
    0 ≤ b * (∫ x, (gaussianPolePosition e g b x - (e + b * v)) ^ 3
      ∂gaussianReal 0 v) := by
  rw [gaussianPolePosition_centered_third]
  have he : b * (6 * b * g ^ 2 * (v : ℝ) ^ 2 + 8 * b ^ 3 * (v : ℝ) ^ 3) =
      6 * b ^ 2 * g ^ 2 * (v : ℝ) ^ 2 + 8 * b ^ 4 * (v : ℝ) ^ 3 := by ring
  rw [he]
  positivity

/-- Non-perturbative spectral law is the distribution of displaced pole positions. -/
def gaussianPoleSpectralMeasure (v : ℝ≥0) (e g b : ℝ) : Measure ℝ :=
  (gaussianReal 0 v).map (gaussianPolePosition e g b)

/-- Equation (20): linear displacement gives an exact Gaussian spectral measure,
including its degenerate zero-variance limit. -/
theorem gaussianPoleSpectralMeasure_linear (v : ℝ≥0) (e g : ℝ) :
    gaussianPoleSpectralMeasure v e g 0 =
      gaussianReal e (⟨g ^ 2, sq_nonneg g⟩ * v) := by
  have hf : gaussianPolePosition e g 0 =
      (fun x : ℝ => e + x) ∘ (fun x : ℝ => g * x) := by
    funext x
    simp [gaussianPolePosition]
  rw [gaussianPoleSpectralMeasure, hf, ← Measure.map_map (by fun_prop) (by fun_prop),
    gaussianReal_map_const_mul, gaussianReal_map_const_add]
  simp [NNReal.mk]

/-- Averaging the two special displacements preserves the exact mean pole shift. -/
theorem gaussianPole_specialDisplacement_mean (v : ℝ≥0) (e g b : ℝ) :
    (gaussianPolePosition e g b (Real.sqrt v) +
      gaussianPolePosition e g b (-Real.sqrt v)) / 2 = e + b * v := by
  unfold gaussianPolePosition
  rw [neg_sq, Real.sq_sqrt v.coe_nonneg]
  ring

/-- The two special displacements erase the entire fluctuation of the quadratic coupling. -/
theorem gaussianPole_specialDisplacement_variance (v : ℝ≥0) (e g b : ℝ) :
    ((gaussianPolePosition e g b (Real.sqrt v) - (e + b * v)) ^ 2 +
      (gaussianPolePosition e g b (-Real.sqrt v) - (e + b * v)) ^ 2) / 2 =
      g ^ 2 * v := by
  unfold gaussianPolePosition
  rw [neg_sq, Real.sq_sqrt v.coe_nonneg]
  calc
    _ = g ^ 2 * Real.sqrt (v : ℝ) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt v.coe_nonneg]

/-- Exact variance lost by replacing Gaussian sampling with the two special displacements. -/
theorem gaussianPole_specialDisplacement_missing_width (v : ℝ≥0) (e g b : ℝ) :
    Var[gaussianPolePosition e g b; gaussianReal 0 v] -
      ((gaussianPolePosition e g b (Real.sqrt v) - (e + b * v)) ^ 2 +
        (gaussianPolePosition e g b (-Real.sqrt v) - (e + b * v)) ^ 2) / 2 =
      2 * b ^ 2 * (v : ℝ) ^ 2 := by
  rw [variance_gaussianPolePosition, gaussianPole_specialDisplacement_variance]
  ring

end GaloisForLFunctions.HTGeometry
