import GaloisForLFunctions.HTGeometry.GaussianPolynomialCoordinateEnergy
import GaloisForLFunctions.HTGeometry.SchwartzQuadratureEnergy

/-!
# Coefficient-uniform quadrature error for polynomial Gaussian energy

The oscillator ceiling absorbs the derivative cross integral into the original
energy. Summing adjacent cells therefore loses only mesh width times the square
root of degree, independently of coefficients and number of sample cells.
-/

open scoped Real SchwartzMap NNReal
open Complex MeasureTheory intervalIntegral
noncomputable section

namespace GaloisForLFunctions

/-- The full derivative cross integral is controlled by the original Gaussian energy. -/
theorem gaussianPolynomial_crossIntegral_le (P : Polynomial ℝ) :
    (∫ u : ℝ, 2 * (‖polyGaussSchwartz P u‖ * ‖derivSCLM (polyGaussSchwartz P) u‖)) ≤
      2 * Real.sqrt (4 * π * ((P.natDegree : ℝ) + 1)) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  let f := polyGaussSchwartz P
  let D := derivSCLM f
  let A := Real.sqrt (4 * π * ((P.natDegree : ℝ) + 1))
  have hA : 0 < A := Real.sqrt_pos.mpr (by positivity)
  have hsq (g : SchwartzMap ℝ ℂ) : Integrable (fun u : ℝ => ‖g u‖ ^ (2 : ℕ)) :=
    (memLp_two_iff_integrable_sq_norm g.continuous.aestronglyMeasurable).mp
      (g.memLp 2 (volume : Measure ℝ))
  have hcross : Integrable (fun u : ℝ => 2 * (‖f u‖ * ‖D u‖)) :=
    ((f.memLp 2 (volume : Measure ℝ)).norm.integrable_mul
      (D.memLp 2 (volume : Measure ℝ)).norm).const_mul 2
  have hpoint (u : ℝ) :
      2 * (‖f u‖ * ‖D u‖) ≤ A * ‖f u‖ ^ 2 + ‖D u‖ ^ 2 / A := by
    apply (mul_le_mul_iff_right₀ hA).mp
    have hcancel : A * (‖D u‖ ^ 2 / A) = ‖D u‖ ^ 2 := by field_simp
    rw [mul_add, hcancel]
    nlinarith only [sq_nonneg (A * ‖f u‖ - ‖D u‖)]
  have hmono := MeasureTheory.integral_mono hcross
    (((hsq f).const_mul A).add ((hsq D).div_const A)) hpoint
  simp only [Pi.add_apply] at hmono
  rw [MeasureTheory.integral_add ((hsq f).const_mul A) ((hsq D).div_const A),
    MeasureTheory.integral_const_mul A (fun u : ℝ => ‖f u‖ ^ (2 : ℕ)),
    MeasureTheory.integral_div A (fun u : ℝ => ‖D u‖ ^ (2 : ℕ)),
    ← norm_toLp_sq_eq_integral f, ← norm_toLp_sq_eq_integral D] at hmono
  have hD := pow_le_pow_left₀ (norm_nonneg _)
    (gaussianPolynomialFullDerivativeNorm_le P) 2
  change ‖D.toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
    (A * ‖f.toLp 2 (volume : Measure ℝ)‖) ^ 2 at hD
  have hdiv : ‖D.toLp 2 (volume : Measure ℝ)‖ ^ 2 / A ≤
      A * ‖f.toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
    apply (div_le_iff₀ hA).mpr
    nlinarith only [hD]
  change (∫ u : ℝ, 2 * (‖f u‖ * ‖D u‖)) ≤
    2 * A * ‖f.toLp 2 (volume : Measure ℝ)‖ ^ 2
  nlinarith only [hmono, hdiv]

/-- Gaussian energy quadrature has mesh times square-root-degree relative error. -/
theorem gaussianPolynomial_grid_quadrature_error (P : Polynomial ℝ) (a : ℝ) (h : ℝ≥0)
    (s : ℕ → Set.Icc (0 : ℝ) 1) (N : ℕ) :
    |(∫ u in a..a + (N : ℝ) * h, ‖polyGaussSchwartz P u‖ ^ 2) -
        (h : ℝ) * ∑ j ∈ Finset.range N,
          ‖polyGaussSchwartz P (a + ((j : ℝ) + (s j : ℝ)) * h)‖ ^ 2| ≤
      2 * (h : ℝ) * Real.sqrt (4 * π * ((P.natDegree : ℝ) + 1)) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  let f := polyGaussSchwartz P
  have hcross : Integrable (fun u : ℝ => 2 * (‖f u‖ * ‖derivSCLM f u‖)) :=
    ((f.memLp 2 (volume : Measure ℝ)).norm.integrable_mul
      ((derivSCLM f).memLp 2 (volume : Measure ℝ)).norm).const_mul 2
  have hlocal : (∫ u in a..a + (N : ℝ) * h, 2 * (‖f u‖ * ‖derivSCLM f u‖)) ≤
      ∫ u : ℝ, 2 * (‖f u‖ * ‖derivSCLM f u‖) := by
    rw [integral_of_le (le_add_of_nonneg_right (by positivity : 0 ≤ (N : ℝ) * h))]
    exact setIntegral_le_integral hcross (Filter.Eventually.of_forall fun _ => by positivity)
  calc
    _ ≤ (h : ℝ) * (∫ u in a..a + (N : ℝ) * h, 2 * (‖f u‖ * ‖derivSCLM f u‖)) :=
      schwartzEnergy_grid_quadrature_error f a h s N
    _ ≤ (h : ℝ) * (2 * Real.sqrt (4 * π * ((P.natDegree : ℝ) + 1)) *
        ‖f.toLp 2 (volume : Measure ℝ)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hlocal.trans (gaussianPolynomial_crossIntegral_le P)) h.coe_nonneg
    _ = _ := by ring

end GaloisForLFunctions
