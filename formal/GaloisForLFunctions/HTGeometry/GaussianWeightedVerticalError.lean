import GaloisForLFunctions.HTGeometry.GaussianStripSamplingError

/-!
# Coordinate-weighted error of an entire polynomial Gaussian

The exact coordinate transport identity retains both the translated polynomial
and the Gaussian phase. Singleton sampling and the oscillator coordinate bound
give a coefficient-uniform error with reciprocal-coordinate decay.
-/

open scoped Real SchwartzMap NNReal
open Complex MeasureTheory
noncomputable section

namespace GaloisForLFunctions

/-- The complete polynomial Gaussian, evaluated before taking any norm. -/
def entirePolynomialGaussian (P : Polynomial ℝ) (z : ℂ) : ℂ :=
  P.eval₂ (algebraMap ℝ ℂ) z * Complex.exp (-(π : ℂ) * z ^ 2)

theorem entirePolynomialGaussian_real (P : Polynomial ℝ) (x : ℝ) :
    entirePolynomialGaussian P x = polyGaussSchwartz P x := by
  have he := Polynomial.eval₂_at_apply (p := P) (algebraMap ℝ ℂ) x
  simpa [entirePolynomialGaussian, polyGaussSchwartz_apply, gaussReal,
    Complex.ofReal_exp] using he

/-- Multiplying the polynomial by its variable multiplies the entire amplitude. -/
theorem entirePolynomialGaussian_mul_X (P : Polynomial ℝ) (z : ℂ) :
    entirePolynomialGaussian (Polynomial.X * P) z = z * entirePolynomialGaussian P z := by
  simp only [entirePolynomialGaussian, Polynomial.eval₂_mul, Polynomial.eval₂_X]
  ring

/-- Exact transport: no imaginary shift or phase cross term is discarded. -/
theorem entirePolynomialGaussian_coordinate_error (P : Polynomial ℝ) (x δ : ℝ) :
    (x : ℂ) * (entirePolynomialGaussian P ((x : ℂ) + (δ : ℂ) * Complex.I) -
        polyGaussSchwartz P x) =
      (entirePolynomialGaussian (Polynomial.X * P) ((x : ℂ) + (δ : ℂ) * Complex.I) -
        polyGaussSchwartz (Polynomial.X * P) x) -
          (δ : ℂ) * Complex.I * entirePolynomialGaussian P ((x : ℂ) + (δ : ℂ) * Complex.I) := by
  rw [← entirePolynomialGaussian_real, ← entirePolynomialGaussian_real,
    entirePolynomialGaussian_mul_X, entirePolynomialGaussian_mul_X]
  ring

theorem verticalPolynomialGaussianDefect_nonneg (d : ℕ) (δ : ℝ) :
    0 ≤ verticalPolynomialGaussianDefect d δ := by
  unfold verticalPolynomialGaussianDefect
  have h₁ : 0 ≤ Real.exp (|δ| * Real.sqrt (4 * π * d)) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have h₂ : 0 ≤ Real.exp (π * δ ^ 2) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (by positivity))
  positivity

/-- Increasing the degree ceiling only enlarges the complete defect. -/
theorem verticalPolynomialGaussianDefect_mono (δ : ℝ) :
    Monotone (fun d : ℕ => verticalPolynomialGaussianDefect d δ) := by
  intro d e hde
  have hc : (d : ℝ) ≤ (e : ℝ) := by exact_mod_cast hde
  unfold verticalPolynomialGaussianDefect
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply add_le_add
  · apply sub_le_sub_right
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hc (by positivity))
  · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (add_le_add hc le_rfl) (by positivity))

theorem gaussianStripSamplingFactor_mono (h : ℝ≥0) :
    Monotone (fun d : ℕ => gaussianStripSamplingFactor d h) := by
  intro d e hde
  have hc : (d : ℝ) ≤ (e : ℝ) := by exact_mod_cast hde
  unfold gaussianStripSamplingFactor
  apply Real.sqrt_le_sqrt
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (add_le_add hc le_rfl) (by positivity))

/-- A singleton unit grid gives the exact point-evaluation norm. -/
theorem norm_gaussianGridSamples_singleton (x : ℝ) (f : ℝ → ℂ) :
    ‖gaussianGridSamples x 1 (fun _ => ⟨0, by simp⟩) 1 f‖ = ‖f x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [gaussianGridSamples_norm_sq]
  simp

/-- Complete polynomial point values have a coefficient-uniform Gaussian norm ceiling. -/
theorem norm_polyGaussSchwartz_point_le (P : Polynomial ℝ) (x : ℝ) :
    ‖polyGaussSchwartz P x‖ ≤ gaussianStripSamplingFactor P.natDegree 1 *
      ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  simpa only [norm_gaussianGridSamples_singleton] using
    norm_gaussianGridSamples_polyGauss_le_stripFactor P x 1 (fun _ => ⟨0, by simp⟩) 1

/-- The strip error has a uniform pointwise ceiling before any coordinate weighting. -/
theorem norm_entirePolynomialGaussian_vertical_sub_le (P : Polynomial ℝ) (R : ℝ≥0)
    (x : ℝ) (δ : Set.Icc (-(R : ℝ)) R) :
    ‖entirePolynomialGaussian P ((x : ℂ) + ((δ : ℝ) : ℂ) * Complex.I) -
        polyGaussSchwartz P x‖ ≤
      gaussianStripSamplingFactor P.natDegree 1 * verticalPolynomialGaussianDefect P.natDegree R *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  refine (norm_polynomialGaussian_vertical_sub_le_envelope P R x δ).trans ?_
  have h := norm_gaussianGridSamples_stripEnvelope_le P R x 1 (fun _ => ⟨0, by simp⟩) 1
  simpa only [norm_gaussianGridSamples_singleton, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gaussianVerticalStripEnvelope_nonneg P R x)] using h

/-- A degree-only weighted defect, vanishing with strip radius. -/
def gaussianCoordinateVerticalDefect (d : ℕ) (R : ℝ≥0) : ℝ :=
  gaussianStripSamplingFactor (d + 1) 1 * verticalPolynomialGaussianDefect (d + 1) R *
      (Real.sqrt (4 * π * ((d : ℝ) + 1)) / (2 * π)) +
    (R : ℝ) * gaussianStripSamplingFactor d 1 * (verticalPolynomialGaussianDefect d R + 1)

theorem gaussianCoordinateVerticalDefect_nonneg (d : ℕ) (R : ℝ≥0) :
    0 ≤ gaussianCoordinateVerticalDefect d R := by
  unfold gaussianCoordinateVerticalDefect
  exact add_nonneg
    (mul_nonneg (mul_nonneg (gaussianStripSamplingFactor_nonneg _ _)
      (verticalPolynomialGaussianDefect_nonneg _ _)) (by positivity))
    (mul_nonneg (mul_nonneg R.coe_nonneg (gaussianStripSamplingFactor_nonneg _ _))
      (add_nonneg (verticalPolynomialGaussianDefect_nonneg _ _) (by positivity)))

/-- The full vertical error decays at least reciprocally in the real coordinate. -/
theorem abs_mul_norm_entirePolynomialGaussian_vertical_sub_le (P : Polynomial ℝ) (R : ℝ≥0)
    (x : ℝ) (δ : Set.Icc (-(R : ℝ)) R) :
    |x| * ‖entirePolynomialGaussian P ((x : ℂ) + ((δ : ℝ) : ℂ) * Complex.I) -
        polyGaussSchwartz P x‖ ≤
      gaussianCoordinateVerticalDefect P.natDegree R *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  let M : ℝ := ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖
  let z : ℂ := (x : ℂ) + ((δ : ℝ) : ℂ) * Complex.I
  have hd : (Polynomial.X * P).natDegree ≤ P.natDegree + 1 := by
    simpa only [Polynomial.natDegree_X, add_comm] using
      Polynomial.natDegree_mul_le (p := (Polynomial.X : Polynomial ℝ)) (q := P)
  have hcoef := mul_le_mul
    (gaussianStripSamplingFactor_mono 1 hd) (verticalPolynomialGaussianDefect_mono R hd)
    (verticalPolynomialGaussianDefect_nonneg _ _) (gaussianStripSamplingFactor_nonneg _ _)
  have hcoord : ‖(polyGaussSchwartz (Polynomial.X * P)).toLp 2 (volume : Measure ℝ)‖ ≤
      (Real.sqrt (4 * π * ((P.natDegree : ℝ) + 1)) / (2 * π)) * M := by
    rw [← mulXCLM_polyGauss_eq, div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * π)).mpr
    simpa only [M, mul_comm] using gaussianPolynomialCoordinateNorm_le P
  have hXP := (norm_entirePolynomialGaussian_vertical_sub_le (Polynomial.X * P) R x δ).trans
    (mul_le_mul hcoef hcoord (norm_nonneg _) (mul_nonneg
      (gaussianStripSamplingFactor_nonneg _ _) (verticalPolynomialGaussianDefect_nonneg _ _)))
  have hP := norm_entirePolynomialGaussian_vertical_sub_le P R x δ
  have hbase := norm_polyGaussSchwartz_point_le P x
  have hz : ‖entirePolynomialGaussian P z‖ ≤
      gaussianStripSamplingFactor P.natDegree 1 * (verticalPolynomialGaussianDefect P.natDegree R + 1) * M := by
    have ht := norm_le_norm_sub_add (entirePolynomialGaussian P z) (polyGaussSchwartz P x)
    change ‖entirePolynomialGaussian P z - polyGaussSchwartz P x‖ ≤ _ at hP
    nlinarith only [ht, hP, hbase]
  have hδ : |(δ : ℝ)| ≤ (R : ℝ) := abs_le.mpr δ.property
  have ht := norm_sub_le
    (entirePolynomialGaussian (Polynomial.X * P) z - polyGaussSchwartz (Polynomial.X * P) x)
    (((δ : ℝ) : ℂ) * Complex.I * entirePolynomialGaussian P z)
  rw [← entirePolynomialGaussian_coordinate_error P x δ, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, mul_one] at ht
  have hv := mul_le_mul hδ hz (norm_nonneg _) (by positivity)
  unfold gaussianCoordinateVerticalDefect
  change _ ≤ _ * M
  nlinarith only [ht, hXP, hv]

end GaloisForLFunctions
