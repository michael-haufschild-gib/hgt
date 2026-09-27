import GaloisForLFunctions.HTGeometry.GaussianPolynomialSamplingError
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Upper Gaussian sampling energy on arbitrary in-cell grids

The whole polynomial energy controls samples in adjacent cells, independently
of the number of cells. The Hilbert-space formulation preserves polynomial
cross terms and supports pointwise-envelope estimates by the triangle inequality.
-/

open scoped Real SchwartzMap NNReal
open Complex MeasureTheory intervalIntegral
noncomputable section

namespace GaloisForLFunctions

/-- Grid energy is bounded by continuous energy with a square-root-degree mesh loss. -/
theorem gaussianPolynomial_grid_energy_upper (P : Polynomial ℝ) (a : ℝ) (h : ℝ≥0)
    (s : ℕ → Set.Icc (0 : ℝ) 1) (N : ℕ) :
    (h : ℝ) * (∑ j ∈ Finset.range N,
      ‖polyGaussSchwartz P (a + ((j : ℝ) + (s j : ℝ)) * h)‖ ^ 2) ≤
      (1 + 2 * (h : ℝ) * Real.sqrt (4 * π * ((P.natDegree : ℝ) + 1))) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  have hquad := (abs_le.mp (gaussianPolynomial_grid_quadrature_error P a h s N)).1
  have hi : Integrable (fun x : ℝ => ‖polyGaussSchwartz P x‖ ^ (2 : ℕ)) :=
    (memLp_two_iff_integrable_sq_norm (polyGaussSchwartz P).continuous.aestronglyMeasurable).mp
      ((polyGaussSchwartz P).memLp 2 (volume : Measure ℝ))
  have hlocal : (∫ x in a..a + (N : ℝ) * h, ‖polyGaussSchwartz P x‖ ^ 2) ≤
      ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
    rw [integral_of_le (le_add_of_nonneg_right (by positivity : 0 ≤ (N : ℝ) * h)),
      norm_toLp_sq_eq_integral]
    exact setIntegral_le_integral hi (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  nlinarith only [hquad, hlocal]

/-- Weighted samples as a finite Hilbert-space vector. -/
def gaussianGridSamples (a : ℝ) (h : ℝ≥0) (s : ℕ → Set.Icc (0 : ℝ) 1)
    (N : ℕ) (f : ℝ → ℂ) : EuclideanSpace ℂ (Fin N) :=
  Real.sqrt (h : ℝ) • WithLp.toLp 2 (fun j : Fin N =>
    f (a + ((j : ℝ) + (s j : ℝ)) * h))

/-- The grid norm is exactly the complete weighted sum of evaluation squares. -/
theorem gaussianGridSamples_norm_sq (a : ℝ) (h : ℝ≥0)
    (s : ℕ → Set.Icc (0 : ℝ) 1) (N : ℕ) (f : ℝ → ℂ) :
    ‖gaussianGridSamples a h s N f‖ ^ 2 =
      (h : ℝ) * ∑ j ∈ Finset.range N, ‖f (a + ((j : ℝ) + (s j : ℝ)) * h)‖ ^ 2 := by
  rw [gaussianGridSamples, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt h.coe_nonneg,
    PiLp.norm_sq_eq_of_L2]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun j : ℕ => ‖f (a + ((j : ℝ) + (s j : ℝ)) * h)‖ ^ 2) N

/-- The Gaussian grid operator has a coefficient-uniform norm bound. -/
theorem norm_gaussianGridSamples_polyGauss_le (P : Polynomial ℝ) (a : ℝ) (h : ℝ≥0)
    (s : ℕ → Set.Icc (0 : ℝ) 1) (N : ℕ) :
    ‖gaussianGridSamples a h s N (polyGaussSchwartz P)‖ ≤
      Real.sqrt (1 + 2 * (h : ℝ) * Real.sqrt (4 * π * ((P.natDegree : ℝ) + 1))) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [gaussianGridSamples_norm_sq, mul_pow, Real.sq_sqrt (by positivity)]
  exact gaussianPolynomial_grid_energy_upper P a h s N

end GaloisForLFunctions
