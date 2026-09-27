import GaloisForLFunctions.HTGeometry.GaussianPolynomialSamplingUpper

/-!
# Linear and norm identities for weighted Gaussian-grid sampling

The sampling map is linear on complete functions. Replacing an evaluation by
its nonnegative norm preserves the sample energy, which allows a simultaneous
pointwise envelope to be estimated in the same finite Hilbert space.
-/

open scoped Real SchwartzMap NNReal
open Complex MeasureTheory
noncomputable section

namespace GaloisForLFunctions

/-- Weighted evaluation as a complex-linear map into finite Hilbert space. -/
def gaussianGridSamplingLM (a : ℝ) (h : ℝ≥0) (s : ℕ → Set.Icc (0 : ℝ) 1)
    (N : ℕ) : (ℝ → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) where
  toFun := gaussianGridSamples a h s N
  map_add' f g := by
    ext j
    simp only [gaussianGridSamples, PiLp.smul_apply,
      Pi.add_apply, PiLp.add_apply, smul_add]
  map_smul' c f := by
    ext j
    simp only [gaussianGridSamples, PiLp.smul_apply,
      Pi.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

/-- Sampling a full function sum is exactly the sum of sample vectors. -/
theorem gaussianGridSamples_add (a : ℝ) (h : ℝ≥0) (s : ℕ → Set.Icc (0 : ℝ) 1)
    (N : ℕ) (f g : ℝ → ℂ) :
    gaussianGridSamples a h s N (fun x => f x + g x) =
      gaussianGridSamples a h s N f + gaussianGridSamples a h s N g :=
  (gaussianGridSamplingLM a h s N).map_add f g

/-- Scalar multiplication commutes with complete grid sampling. -/
theorem gaussianGridSamples_smul (a : ℝ) (h : ℝ≥0) (s : ℕ → Set.Icc (0 : ℝ) 1)
    (N : ℕ) (c : ℂ) (f : ℝ → ℂ) :
    gaussianGridSamples a h s N (fun x => c * f x) =
      c • gaussianGridSamples a h s N f :=
  (gaussianGridSamplingLM a h s N).map_smul c f

/-- Every summand in a finite envelope remains present after sampling. -/
theorem gaussianGridSamples_sum {ι : Type*} (a : ℝ) (h : ℝ≥0)
    (s : ℕ → Set.Icc (0 : ℝ) 1) (N : ℕ) (J : Finset ι) (f : ι → ℝ → ℂ) :
    gaussianGridSamples a h s N (fun x => ∑ k ∈ J, f k x) =
      ∑ k ∈ J, gaussianGridSamples a h s N (f k) := by
  change (gaussianGridSamplingLM a h s N) (fun x => ∑ k ∈ J, f k x) =
    ∑ k ∈ J, (gaussianGridSamplingLM a h s N) (f k)
  simpa only [Finset.sum_fn] using map_sum (gaussianGridSamplingLM a h s N) f J

/-- Absolute values taken after evaluation preserve the exact grid energy. -/
theorem norm_gaussianGridSamples_norm (a : ℝ) (h : ℝ≥0)
    (s : ℕ → Set.Icc (0 : ℝ) 1) (N : ℕ) (f : ℝ → ℂ) :
    ‖gaussianGridSamples a h s N (fun x => (‖f x‖ : ℂ))‖ =
      ‖gaussianGridSamples a h s N f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [gaussianGridSamples_norm_sq, gaussianGridSamples_norm_sq]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]

/-- Coordinate multiplication of a full Gaussian is exactly multiplication of its polynomial. -/
theorem mulXCLM_polyGauss_eq (P : Polynomial ℝ) :
    mulXCLM (polyGaussSchwartz P) = polyGaussSchwartz (Polynomial.X * P) := by
  ext x
  simp only [mulXCLM_apply, polyGaussSchwartz_apply, Polynomial.eval_mul, Polynomial.eval_X]
  push_cast
  ring

end GaloisForLFunctions
