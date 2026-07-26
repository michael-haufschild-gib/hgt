/-
# Osculating geometry of Bourgain's square-root curve

For the curve `(t,t²,t^(3/2),t^(1/2))`, the change of variables in
Bourgain (1.23)--(1.24) uses first and second jets at two separated points.
Writing those points as `a²` and `b²`, this file computes the determinant of
the resulting jet matrix exactly:

`det = 3 (b-a)^4 / (8 a^3 b^3)`.

Thus the change of variables is unconditionally invertible whenever
`0 < a < b`.
-/
import GaloisForLFunctions.RHTower.BourgainPhasePerturbation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace RHTower

noncomputable section

set_option maxHeartbeats 1000000

/-- Literal first/second derivative matrix of Bourgain's square-root curve. -/
def bourgainSquareRootCurveDerivativeMatrix
    (s t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![iteratedDeriv 1 (fun x : ℝ => x) s,
       iteratedDeriv 2 (fun x : ℝ => x) s,
       iteratedDeriv 1 (fun x : ℝ => x) t,
       iteratedDeriv 2 (fun x : ℝ => x) t;
     iteratedDeriv 1 (fun x : ℝ => x ^ (2 : ℕ)) s,
       iteratedDeriv 2 (fun x : ℝ => x ^ (2 : ℕ)) s,
       iteratedDeriv 1 (fun x : ℝ => x ^ (2 : ℕ)) t,
       iteratedDeriv 2 (fun x : ℝ => x ^ (2 : ℕ)) t;
     iteratedDeriv 1 (fun x : ℝ => x ^ (3 / 2 : ℝ)) s,
       iteratedDeriv 2 (fun x : ℝ => x ^ (3 / 2 : ℝ)) s,
       iteratedDeriv 1 (fun x : ℝ => x ^ (3 / 2 : ℝ)) t,
       iteratedDeriv 2 (fun x : ℝ => x ^ (3 / 2 : ℝ)) t;
     iteratedDeriv 1 (fun x : ℝ => x ^ (1 / 2 : ℝ)) s,
       iteratedDeriv 2 (fun x : ℝ => x ^ (1 / 2 : ℝ)) s,
       iteratedDeriv 1 (fun x : ℝ => x ^ (1 / 2 : ℝ)) t,
       iteratedDeriv 2 (fun x : ℝ => x ^ (1 / 2 : ℝ)) t]

/-- First derivative of `t^(3/2)` at `t=a²`. -/
theorem iteratedDeriv_rpow_three_halves_one_sq
    {a : ℝ} (ha : 0 < a) :
    iteratedDeriv 1 (fun x : ℝ => x ^ (3 / 2 : ℝ)) (a ^ 2) =
      3 * a / 2 := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
  norm_num
  rw [show (a ^ 2 : ℝ) ^ (1 / 2 : ℝ) = a by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_sq_eq_abs a |>.trans (abs_of_pos ha)]
  ring

/-- Second derivative of `t^(3/2)` at `t=a²`. -/
theorem iteratedDeriv_rpow_three_halves_two_sq
    {a : ℝ} (ha : 0 < a) :
    iteratedDeriv 2 (fun x : ℝ => x ^ (3 / 2 : ℝ)) (a ^ 2) =
      3 / (4 * a) := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
  norm_num [descPochhammer]
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hpow : (a ^ 2 : ℝ) ^ (-(1 / 2 : ℝ)) = a⁻¹ := by
    rw [Real.rpow_neg ha2.le, ← Real.sqrt_eq_rpow,
      Real.sqrt_sq_eq_abs, abs_of_pos ha]
  rw [hpow]
  field_simp

/-- First derivative of `t^(1/2)` at `t=a²`. -/
theorem iteratedDeriv_rpow_half_one_sq
    {a : ℝ} (ha : 0 < a) :
    iteratedDeriv 1 (fun x : ℝ => x ^ (1 / 2 : ℝ)) (a ^ 2) =
      1 / (2 * a) := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
  norm_num
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hpow : (a ^ 2 : ℝ) ^ (-(1 / 2 : ℝ)) = a⁻¹ := by
    rw [Real.rpow_neg ha2.le, ← Real.sqrt_eq_rpow,
      Real.sqrt_sq_eq_abs, abs_of_pos ha]
  rw [hpow]
  field_simp

/-- Second derivative of `t^(1/2)` at `t=a²`. -/
theorem iteratedDeriv_rpow_half_two_sq
    {a : ℝ} (ha : 0 < a) :
    iteratedDeriv 2 (fun x : ℝ => x ^ (1 / 2 : ℝ)) (a ^ 2) =
      -1 / (4 * a ^ 3) := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
  norm_num [descPochhammer]
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hpow : (a ^ 2 : ℝ) ^ (-(3 / 2 : ℝ)) = a⁻¹ ^ 3 := by
    rw [show -(3 / 2 : ℝ) = (-(1 / 2 : ℝ)) * 3 by ring,
      Real.rpow_mul ha2.le]
    rw [Real.rpow_neg ha2.le, ← Real.sqrt_eq_rpow,
      Real.sqrt_sq_eq_abs, abs_of_pos ha]
    exact Real.rpow_natCast (a⁻¹) 3
  rw [hpow]
  field_simp

/-- First/second jet matrix of `(t,t²,t^(3/2),t^(1/2))` at the parameters
`a²` and `b²`.  Columns are `Φ'(a²), Φ''(a²), Φ'(b²), Φ''(b²)`. -/
def bourgainSquareRootOsculatingMatrix
    (a b : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 1, 0;
     2 * a ^ 2, 2, 2 * b ^ 2, 2;
     3 * a / 2, 3 / (4 * a), 3 * b / 2, 3 / (4 * b);
     1 / (2 * a), -1 / (4 * a ^ 3),
       1 / (2 * b), -1 / (4 * b ^ 3)]

/-- The displayed osculating matrix is exactly the derivative matrix of the
curve, rather than an independent algebraic model. -/
theorem bourgainSquareRootCurveDerivativeMatrix_sq
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    bourgainSquareRootCurveDerivativeMatrix (a ^ 2) (b ^ 2) =
      bourgainSquareRootOsculatingMatrix a b := by
  ext i j
  fin_cases i
  · fin_cases j <;>
      norm_num [bourgainSquareRootCurveDerivativeMatrix,
        bourgainSquareRootOsculatingMatrix, iteratedDeriv_eq_iterate]
  · fin_cases j <;>
      norm_num [bourgainSquareRootCurveDerivativeMatrix,
        bourgainSquareRootOsculatingMatrix, iteratedDeriv_eq_iterate,
        iter_deriv_pow]
  · fin_cases j
    · simpa [bourgainSquareRootCurveDerivativeMatrix,
        bourgainSquareRootOsculatingMatrix] using
        iteratedDeriv_rpow_three_halves_one_sq ha
    · simpa [bourgainSquareRootCurveDerivativeMatrix,
        bourgainSquareRootOsculatingMatrix] using
        iteratedDeriv_rpow_three_halves_two_sq ha
    · simpa [bourgainSquareRootCurveDerivativeMatrix,
        bourgainSquareRootOsculatingMatrix] using
        iteratedDeriv_rpow_three_halves_one_sq hb
    · simpa [bourgainSquareRootCurveDerivativeMatrix,
        bourgainSquareRootOsculatingMatrix] using
        iteratedDeriv_rpow_three_halves_two_sq hb
  · fin_cases j
    · simpa [bourgainSquareRootCurveDerivativeMatrix,
        bourgainSquareRootOsculatingMatrix] using
        iteratedDeriv_rpow_half_one_sq ha
    · simpa [bourgainSquareRootCurveDerivativeMatrix,
        bourgainSquareRootOsculatingMatrix] using
        iteratedDeriv_rpow_half_two_sq ha
    · simpa [bourgainSquareRootCurveDerivativeMatrix,
        bourgainSquareRootOsculatingMatrix] using
        iteratedDeriv_rpow_half_one_sq hb
    · simpa [bourgainSquareRootCurveDerivativeMatrix,
        bourgainSquareRootOsculatingMatrix] using
        iteratedDeriv_rpow_half_two_sq hb

/-- Exact determinant behind the linear homeomorphism in Bourgain (1.24). -/
theorem det_bourgainSquareRootOsculatingMatrix
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (bourgainSquareRootOsculatingMatrix a b).det =
      3 * (b - a) ^ (4 : ℕ) / (8 * a ^ (3 : ℕ) * b ^ (3 : ℕ)) := by
  have h21 : (2 : Fin 4).succAbove (1 : Fin 3) = 1 := by decide
  have h22 : (2 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  rw [Matrix.det_succ_row_zero]
  simp [bourgainSquareRootOsculatingMatrix, Matrix.det_fin_three,
    Fin.sum_univ_four, h21, h22]
  field_simp
  ring

/-- Exact determinant stated directly for the curve's first/second
derivatives. -/
theorem det_bourgainSquareRootCurveDerivativeMatrix_sq
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (bourgainSquareRootCurveDerivativeMatrix (a ^ 2) (b ^ 2)).det =
      3 * (b - a) ^ (4 : ℕ) /
        (8 * a ^ (3 : ℕ) * b ^ (3 : ℕ)) := by
  rw [bourgainSquareRootCurveDerivativeMatrix_sq ha hb,
    det_bourgainSquareRootOsculatingMatrix ha.ne' hb.ne']

/-- Quantitative positivity for separated positive square-root parameters. -/
theorem det_bourgainSquareRootOsculatingMatrix_pos
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < (bourgainSquareRootOsculatingMatrix a b).det := by
  rw [det_bourgainSquareRootOsculatingMatrix ha.ne'
    (lt_trans ha hab).ne']
  exact div_pos
    (mul_pos (by norm_num) (pow_pos (sub_pos.mpr hab) 4))
    (mul_pos (mul_pos (by norm_num) (pow_pos ha 3))
      (pow_pos (lt_trans ha hab) 3))

/-- The osculating jet matrix is a unit over `ℝ`. -/
theorem isUnit_bourgainSquareRootOsculatingMatrix
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IsUnit (bourgainSquareRootOsculatingMatrix a b) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact ne_of_gt (det_bourgainSquareRootOsculatingMatrix_pos ha hab)

/-- Injectivity of Bourgain's jet-coordinate change. -/
theorem bourgainSquareRootOsculatingMatrix_mulVec_injective
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Function.Injective
      (bourgainSquareRootOsculatingMatrix a b).mulVec := by
  exact Matrix.mulVec_injective_iff_isUnit.mpr
    (isUnit_bourgainSquareRootOsculatingMatrix ha hab)

/-- Surjectivity of Bourgain's jet-coordinate change. -/
theorem bourgainSquareRootOsculatingMatrix_mulVec_surjective
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Function.Surjective
      (bourgainSquareRootOsculatingMatrix a b).mulVec := by
  exact Matrix.mulVec_surjective_iff_isUnit.mpr
    (isUnit_bourgainSquareRootOsculatingMatrix ha hab)

/-- Linear equivalence for the unscaled first/second-jet matrix.
`BourgainOsculatingPhaseCoordinates` inserts the two `1/2` factors from the
literal phase coordinates in (1.23)--(1.24). -/
noncomputable def bourgainSquareRootOsculatingLinearEquiv
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearEquiv.ofBijective
    (bourgainSquareRootOsculatingMatrix a b).mulVecLin
    ⟨bourgainSquareRootOsculatingMatrix_mulVec_injective ha hab,
      bourgainSquareRootOsculatingMatrix_mulVec_surjective ha hab⟩

/-- In finite dimension, Bourgain's coordinate change is a continuous linear
homeomorphism. -/
noncomputable def bourgainSquareRootOsculatingContinuousLinearEquiv
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ) :=
  (bourgainSquareRootOsculatingLinearEquiv ha hab).toContinuousLinearEquiv

/-- Exact Lebesgue-measure Jacobian for the unscaled jet matrix.  The literal
phase-coordinate Jacobian, including both second-derivative half factors, is
proved in `BourgainOsculatingPhaseCoordinates`. -/
theorem map_bourgainSquareRootOsculatingMatrix_volume
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MeasureTheory.Measure.map
        (Matrix.toLin' (bourgainSquareRootOsculatingMatrix a b))
        MeasureTheory.volume =
      ENNReal.ofReal
          |(3 * (b - a) ^ (4 : ℕ) /
            (8 * a ^ (3 : ℕ) * b ^ (3 : ℕ)))⁻¹| •
        MeasureTheory.volume := by
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi
    (ne_of_gt (det_bourgainSquareRootOsculatingMatrix_pos ha hab))]
  rw [det_bourgainSquareRootOsculatingMatrix ha.ne'
    (lt_trans ha hab).ne']

end

end RHTower
