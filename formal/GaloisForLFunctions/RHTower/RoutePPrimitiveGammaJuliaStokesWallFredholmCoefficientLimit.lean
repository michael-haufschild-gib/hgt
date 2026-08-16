import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallCubicKernelL2Limit
import GaloisForLFunctions.HTGeometry.ContinuousKernelFredholmDeterminant
import Mathlib.Probability.ProductMeasure

/-!
# P-G105W: every fixed SP-E Fredholm coefficient has an exponential wall limit

The quantile pullback places every moving prime wall law on one fixed finite cube.  At each
Fredholm order, every matrix entry converges to the mean-one exponential quantile kernel.
Expanding the determinant gives pointwise convergence of the complete signed-permutation sum;
Hadamard's inequality supplies a dimension-sharp constant dominator.  Dominated convergence then
proves convergence of every factorial-normalized coefficient, with no truncation of permutations,
prime incidences, or determinant orders.

Transport from these quantile coefficients to the finite child determinant, and passage from
fixed coefficients to a locally uniform entire determinant limit, remain separate gates.
-/

open Complex Filter Topology Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace RHTower

noncomputable section

/-- Product Lebesgue measure on the open unit `n`-cube. -/
def routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure (n : ℕ) :
    Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => volume.restrict (Ioo (0 : ℝ) 1))

instance instIsFiniteMeasureRoutePPrimitiveGammaJuliaStokesWallUnitCubeMeasure (n : ℕ) :
    IsFiniteMeasure (routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure n) := by
  unfold routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure
  infer_instance

/-- Quantile-pulled cubic wall matrix at Fredholm order `n`. -/
def routePPrimitiveGammaJuliaStokesWallFredholmMatrix
    (μ : Measure ℝ) (n : ℕ) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    (routePPrimitiveGammaJuliaStokesWallQuantileKernel μ (x i, x j) : ℂ)

/-- Complete signed-permutation determinant integrand at Fredholm order `n`. -/
def routePPrimitiveGammaJuliaStokesWallFredholmIntegrand
    (μ : Measure ℝ) (n : ℕ) (x : Fin n → ℝ) : ℂ :=
  Matrix.det (routePPrimitiveGammaJuliaStokesWallFredholmMatrix μ n x)

theorem measurable_routePPrimitiveGammaJuliaStokesWallFredholmIntegrand
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    Measurable (routePPrimitiveGammaJuliaStokesWallFredholmIntegrand μ n) := by
  classical
  unfold routePPrimitiveGammaJuliaStokesWallFredholmIntegrand
    routePPrimitiveGammaJuliaStokesWallFredholmMatrix
  simp only [Matrix.det_apply']
  apply Finset.measurable_sum
  intro σ hσ
  apply Measurable.mul measurable_const
  apply Finset.measurable_prod
  intro i hi
  exact Complex.measurable_ofReal.comp
    ((measurable_routePPrimitiveGammaJuliaStokesWallQuantileKernel μ).comp
      ((measurable_pi_apply (σ i)).prodMk (measurable_pi_apply i)))

/-- At every point of every fixed cube, the full signed-permutation determinant converges. -/
theorem tendsto_routePPrimitiveGammaJuliaStokesWallFredholmIntegrand_nhdsGT_zero
    (n : ℕ) (x : Fin n → ℝ) :
    Tendsto
      (fun d : ℝ => routePPrimitiveGammaJuliaStokesWallFredholmIntegrand
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) n x)
      (𝓝[>] (0 : ℝ))
      (𝓝 (routePPrimitiveGammaJuliaStokesWallFredholmIntegrand
        (expMeasure 1) n x)) := by
  classical
  unfold routePPrimitiveGammaJuliaStokesWallFredholmIntegrand
    routePPrimitiveGammaJuliaStokesWallFredholmMatrix
  simp only [Matrix.det_apply']
  apply tendsto_finsetSum Finset.univ
  intro σ hσ
  apply Tendsto.mul tendsto_const_nhds
  apply tendsto_finsetProd Finset.univ
  intro i hi
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_routePPrimitiveGammaJuliaStokesWallQuantileKernel_nhdsGT_zero
      (x (σ i), x i))

/-- Hadamard domination of the complete order-`n` determinant integrand. -/
theorem norm_routePPrimitiveGammaJuliaStokesWallFredholmIntegrand_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsupp : μ (Iio 0) = 0)
    (n : ℕ) (x : Fin n → ℝ) :
    ‖routePPrimitiveGammaJuliaStokesWallFredholmIntegrand μ n x‖ ≤
      (Real.sqrt n) ^ n := by
  unfold routePPrimitiveGammaJuliaStokesWallFredholmIntegrand
  refine (ContinuousKernelFredholm.complex_hadamard_entry_bound
    (routePPrimitiveGammaJuliaStokesWallFredholmMatrix μ n x) (M := 1) ?_).trans_eq ?_
  · intro i j
    have h := routePPrimitiveGammaJuliaStokesWallQuantileKernel_zero_le_one
      μ hsupp (x i, x j)
    rw [routePPrimitiveGammaJuliaStokesWallFredholmMatrix, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2
  · ring

/-- The complete order-`n` determinant expectation converges to the exponential wall law. -/
theorem tendsto_integral_routePPrimitiveGammaJuliaStokesWallFredholmIntegrand_nhdsGT_zero
    (n : ℕ) :
    Tendsto
      (fun d : ℝ => ∫ x : Fin n → ℝ,
        routePPrimitiveGammaJuliaStokesWallFredholmIntegrand
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) n x
        ∂routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure n)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x : Fin n → ℝ,
        routePPrimitiveGammaJuliaStokesWallFredholmIntegrand
          (expMeasure 1) n x
        ∂routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure n)) := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure one_pos
  apply tendsto_integral_filter_of_dominated_convergence
    (fun _ => (Real.sqrt n) ^ n)
  · exact Filter.Eventually.of_forall fun d =>
      (measurable_routePPrimitiveGammaJuliaStokesWallFredholmIntegrand
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) n).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun d =>
      Filter.Eventually.of_forall fun x =>
        norm_routePPrimitiveGammaJuliaStokesWallFredholmIntegrand_le
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
          (wallHalfLineLaw_Iio_zero d) n x
  · exact integrable_const ((Real.sqrt n) ^ n)
  · exact Filter.Eventually.of_forall fun x =>
      tendsto_routePPrimitiveGammaJuliaStokesWallFredholmIntegrand_nhdsGT_zero n x

/-- Factorial-normalized Fredholm coefficient of a quantile-pulled wall law. -/
def routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
    (μ : Measure ℝ) (n : ℕ) : ℂ :=
  (∫ x : Fin n → ℝ,
      routePPrimitiveGammaJuliaStokesWallFredholmIntegrand μ n x
      ∂routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure n) /
    (n.factorial : ℂ)

/-- Every fixed SP-E Fredholm coefficient converges to its exponential-wall coefficient. -/
theorem tendsto_routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_nhdsGT_zero
    (n : ℕ) :
    Tendsto
      (fun d : ℝ => routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) n)
      (𝓝[>] (0 : ℝ))
      (𝓝 (routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
        (expMeasure 1) n)) := by
  simpa [routePPrimitiveGammaJuliaStokesWallFredholmCoefficient] using
    (tendsto_integral_routePPrimitiveGammaJuliaStokesWallFredholmIntegrand_nhdsGT_zero n).div_const
      (n.factorial : ℂ)

end
end RHTower
