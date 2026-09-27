import GaloisForLFunctions.HTGeometry.GaussianGridHasseEnvelope
import GaloisForLFunctions.HTGeometry.GaussianVerticalStripEnvelope

/-!
# Discrete error for independently displaced polynomial Gaussian samples

The common Hasse and coordinate sampling ceiling controls the simultaneous
strip envelope. Pointwise domination then permits a distinct displacement at
every sample, with no dependence on the number of cells or polynomial coefficients.
-/

open scoped Real SchwartzMap NNReal
open Complex MeasureTheory
noncomputable section

namespace GaloisForLFunctions

/-- The full strip envelope has a coefficient-uniform discrete Hilbert norm bound. -/
theorem norm_gaussianGridSamples_stripEnvelope_le (P : Polynomial ℝ) (R : ℝ≥0)
    (a : ℝ) (h : ℝ≥0) (s : ℕ → Set.Icc (0 : ℝ) 1) (N : ℕ) :
    ‖gaussianGridSamples a h s N (fun x => (gaussianVerticalStripEnvelope P R x : ℂ))‖ ≤
      gaussianStripSamplingFactor P.natDegree h * verticalPolynomialGaussianDefect P.natDegree R *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  let c : ℝ := Real.exp (π * (R : ℝ) ^ 2)
  let b : ℝ := 2 * π * (R : ℝ)
  let C : ℝ := gaussianStripSamplingFactor P.natDegree h
  let M : ℝ := ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖
  let B : ℝ → ℂ := fun x => (gaussianHasseTailEnvelope P R x : ℂ)
  let X : ℝ → ℂ := fun x => (‖mulXCLM (polyGaussSchwartz P) x‖ : ℂ)
  let F : ℝ → ℂ := fun x => (‖polyGaussSchwartz P x‖ : ℂ)
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have hc1 : 0 ≤ c - 1 := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hb : 0 ≤ b := by positivity
  have hscalar : ‖(c : ℂ)‖ = c := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  have hscalar' : ‖((c - 1 : ℝ) : ℂ)‖ = c - 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc1]
  have hscalarb : ‖(b : ℂ)‖ = b := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
  have hid : (fun x => (gaussianVerticalStripEnvelope P R x : ℂ)) =
      fun x => (c : ℂ) * (B x + (b : ℂ) * X x) + ((c - 1 : ℝ) : ℂ) * F x := by
    funext x
    simp only [gaussianVerticalStripEnvelope, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_one, c, b, B, X, F]
  have htriangle :
      ‖gaussianGridSamples a h s N (fun x => (gaussianVerticalStripEnvelope P R x : ℂ))‖ ≤
        c * (‖gaussianGridSamples a h s N B‖ + b * ‖gaussianGridSamples a h s N X‖) +
          (c - 1) * ‖gaussianGridSamples a h s N F‖ := by
    rw [hid, gaussianGridSamples_add, gaussianGridSamples_smul, gaussianGridSamples_smul]
    calc
      _ ≤ ‖(c : ℂ) • gaussianGridSamples a h s N (fun x => B x + (b : ℂ) * X x)‖ +
          ‖((c - 1 : ℝ) : ℂ) • gaussianGridSamples a h s N F‖ := norm_add_le _ _
      _ = c * ‖gaussianGridSamples a h s N (fun x => B x + (b : ℂ) * X x)‖ +
          (c - 1) * ‖gaussianGridSamples a h s N F‖ := by
        rw [norm_smul, norm_smul, hscalar, hscalar']
      _ ≤ _ := by
        apply add_le_add _ le_rfl
        apply mul_le_mul_of_nonneg_left _ hc
        rw [gaussianGridSamples_add, gaussianGridSamples_smul]
        simpa only [norm_smul, hscalarb] using norm_add_le
          (gaussianGridSamples a h s N B) ((b : ℂ) • gaussianGridSamples a h s N X)
  have htail := norm_gaussianGridSamples_hasseEnvelope_le P R a h s N
  have hcoord := norm_gaussianGridSamples_coordinate_le P a h s N
  have hbase := norm_gaussianGridSamples_polyGauss_le_stripFactor P a h s N
  have hnX : ‖gaussianGridSamples a h s N X‖ =
      ‖gaussianGridSamples a h s N (mulXCLM (polyGaussSchwartz P))‖ :=
    norm_gaussianGridSamples_norm a h s N _
  have hnF : ‖gaussianGridSamples a h s N F‖ =
      ‖gaussianGridSamples a h s N (polyGaussSchwartz P)‖ :=
    norm_gaussianGridSamples_norm a h s N _
  rw [hnX, hnF] at htriangle
  change ‖gaussianGridSamples a h s N B‖ ≤
    C * (Real.exp ((R : ℝ) * Real.sqrt (4 * π * P.natDegree)) - 1) * M at htail
  have ht := mul_le_mul_of_nonneg_left htail hc
  have hx := mul_le_mul_of_nonneg_left hcoord (mul_nonneg hc R.coe_nonneg)
  have hf := mul_le_mul_of_nonneg_left hbase hc1
  unfold verticalPolynomialGaussianDefect
  simp only [abs_of_nonneg R.coe_nonneg]
  change _ ≤ C * (c * (Real.exp ((R : ℝ) * Real.sqrt (4 * π * P.natDegree)) - 1 +
    (R : ℝ) * Real.sqrt (4 * π * ((P.natDegree : ℝ) + 1))) + (c - 1)) * M
  dsimp only [b, C, M] at htriangle ht hx hf ⊢
  nlinarith only [htriangle, ht, hx, hf]

/-- Every sample may have its own imaginary displacement; all polynomial terms remain coupled. -/
theorem gaussianPolynomial_grid_variableShift_error (P : Polynomial ℝ) (R : ℝ≥0)
    (a : ℝ) (h : ℝ≥0) (s : ℕ → Set.Icc (0 : ℝ) 1) (N : ℕ)
    (δ : ℕ → Set.Icc (-(R : ℝ)) R) :
    (h : ℝ) * ∑ j ∈ Finset.range N,
      ‖P.eval₂ (algebraMap ℝ ℂ)
          (((a + ((j : ℝ) + (s j : ℝ)) * h : ℝ) : ℂ) + ((δ j : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-(π : ℂ) *
            (((a + ((j : ℝ) + (s j : ℝ)) * h : ℝ) : ℂ) + ((δ j : ℝ) : ℂ) * Complex.I) ^ 2) -
        polyGaussSchwartz P (a + ((j : ℝ) + (s j : ℝ)) * h)‖ ^ 2 ≤
      (1 + 2 * (h : ℝ) * Real.sqrt (4 * π * ((P.natDegree : ℝ) + 2))) *
        verticalPolynomialGaussianDefect P.natDegree R ^ 2 *
          ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  have hsum : (h : ℝ) * ∑ j ∈ Finset.range N,
      ‖P.eval₂ (algebraMap ℝ ℂ)
          (((a + ((j : ℝ) + (s j : ℝ)) * h : ℝ) : ℂ) + ((δ j : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-(π : ℂ) *
            (((a + ((j : ℝ) + (s j : ℝ)) * h : ℝ) : ℂ) + ((δ j : ℝ) : ℂ) * Complex.I) ^ 2) -
        polyGaussSchwartz P (a + ((j : ℝ) + (s j : ℝ)) * h)‖ ^ 2 ≤
      ‖gaussianGridSamples a h s N (fun x => (gaussianVerticalStripEnvelope P R x : ℂ))‖ ^ 2 := by
    rw [gaussianGridSamples_norm_sq]
    apply mul_le_mul_of_nonneg_left _ h.coe_nonneg
    apply Finset.sum_le_sum
    intro j _
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (gaussianVerticalStripEnvelope_nonneg P R _)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_polynomialGaussian_vertical_sub_le_envelope P R _ (δ j)) 2
  have hb := pow_le_pow_left₀ (norm_nonneg _)
    (norm_gaussianGridSamples_stripEnvelope_le P R a h s N) 2
  rw [mul_pow, mul_pow, gaussianStripSamplingFactor,
    Real.sq_sqrt (by positivity)] at hb
  exact hsum.trans hb

end GaloisForLFunctions
