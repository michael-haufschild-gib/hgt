import GaloisForLFunctions.HilbertMetric.Correlation.FiniteGramPrediction
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.ConditionalExpectation

/-!
# Gaussian regression with singular finite observations

Linear observations of a standard Gaussian vector admit the same Gram
pseudoinverse predictor as their Hilbert covariance model. Its residual is
independent of the entire observation vector, including singular observation
maps, and its variance is exactly the squared Hilbert residual norm.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace HilbertMetric.Correlation
variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

local instance : CompleteSpace V := FiniteDimensional.complete ℝ V
local instance : CompleteSpace H := FiniteDimensional.complete ℝ H

private theorem covariance_gaussian_inner (u v : H) :
    cov[fun ω => ⟪u, ω⟫, fun ω => ⟪v, ω⟫; stdGaussian H] = ⟪u, v⟫ := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, innerSL_apply_apply]

/-- The random residual after all finite observations have been used. -/
def gaussianPredictionResidual (Φ : V →L[ℝ] H) (u : H) (ω : H) : ℝ :=
  ⟪u - Φ (finitePredictionCoefficients Φ u), ω⟫

/-- Regression residual and the full observation vector are jointly Gaussian. -/
theorem gaussianPrediction_joint (Φ : V →L[ℝ] H) (u : H) :
    HasGaussianLaw (fun ω => (gaussianPredictionResidual Φ u ω, Φ.adjoint ω))
      (stdGaussian H) :=
  IsGaussian.hasGaussianLaw_id.map
    ((innerSL ℝ (u - Φ (finitePredictionCoefficients Φ u))).prod Φ.adjoint)

/-- The Gaussian prediction residual is independent of all observations, even when their
covariance is singular. -/
theorem gaussianPrediction_residual_independent (Φ : V →L[ℝ] H) (u : H) :
    IndepFun (gaussianPredictionResidual Φ u) Φ.adjoint (stdGaussian H) := by
  apply (gaussianPrediction_joint Φ u).indepFun_of_covariance_inner
  intro x y
  have hx : (fun ω : H => ⟪x, gaussianPredictionResidual Φ u ω⟫) =
      fun ω => ⟪x • (u - Φ (finitePredictionCoefficients Φ u)), ω⟫ := by
    ext ω
    simp only [gaussianPredictionResidual, real_inner_smul_left, RCLike.inner_apply,
      conj_trivial, mul_comm]
  have hy : (fun ω : H => ⟪y, Φ.adjoint ω⟫) = fun ω => ⟪Φ y, ω⟫ := by
    ext ω
    exact ContinuousLinearMap.adjoint_inner_right Φ y ω
  rw [hx, hy, covariance_gaussian_inner, real_inner_smul_left,
    finitePrediction_orthogonal, mul_zero]

omit [MeasurableSpace V] [BorelSpace V] in
/-- The residual is centered under the actual Gaussian measure. -/
theorem gaussianPrediction_residual_mean (Φ : V →L[ℝ] H) (u : H) :
    ∫ ω, gaussianPredictionResidual Φ u ω ∂stdGaussian H = 0 :=
  integral_strongDual_stdGaussian (innerSL ℝ (u - Φ (finitePredictionCoefficients Φ u)))

omit [MeasurableSpace V] [BorelSpace V] in
/-- Gaussian error variance equals the covariance-space prediction risk. -/
theorem gaussianPrediction_error_variance (Φ : V →L[ℝ] H) (u : H) (v : V) :
    Var[fun ω : H => ⟪u, ω⟫ - ⟪v, Φ.adjoint ω⟫; stdGaussian H] = ‖u - Φ v‖ ^ 2 := by
  have he : (fun ω : H => ⟪u, ω⟫ - ⟪v, Φ.adjoint ω⟫) =
      fun ω => ⟪u - Φ v, ω⟫ := by
    ext ω
    rw [ContinuousLinearMap.adjoint_inner_right, inner_sub_left]
  rw [he, ← covariance_self (by fun_prop), covariance_gaussian_inner,
    real_inner_self_eq_norm_sq]

omit [MeasurableSpace V] [BorelSpace V] in
/-- Exact excess Gaussian prediction variance is the squared observed coefficient displacement. -/
theorem gaussianPrediction_variance_decomposition (Φ : V →L[ℝ] H) (u : H) (v : V) :
    Var[fun ω : H => ⟪u, ω⟫ - ⟪v, Φ.adjoint ω⟫; stdGaussian H] =
      Var[gaussianPredictionResidual Φ u; stdGaussian H] +
        ‖Φ (v - finitePredictionCoefficients Φ u)‖ ^ 2 := by
  rw [gaussianPrediction_error_variance, finitePrediction_error_decomposition]
  congr 1
  rw [← covariance_self (by unfold gaussianPredictionResidual; fun_prop)]
  exact ((covariance_gaussian_inner _ _).trans (real_inner_self_eq_norm_sq _)).symm

/-- The Gram predictor is the actual conditional mean given the full observation vector. -/
theorem gaussianPrediction_conditional_mean (Φ : V →L[ℝ] H) (u : H) :
    (stdGaussian H)[(fun ω : H => ⟪u, ω⟫) |
      MeasurableSpace.comap Φ.adjoint inferInstance] =ᵐ[stdGaussian H]
      fun ω => ⟪finitePredictionCoefficients Φ u, Φ.adjoint ω⟫ := by
  let c := finitePredictionCoefficients Φ u
  let r := u - Φ c
  have hm : MeasurableSpace.comap Φ.adjoint inferInstance ≤ ‹MeasurableSpace H› :=
    Φ.adjoint.continuous.measurable.comap_le
  have hR : Measurable (fun ω : H => ⟪r, ω⟫) := by fun_prop
  have hi : IndepFun (fun ω : H => ⟪r, ω⟫) Φ.adjoint (stdGaussian H) :=
    gaussianPrediction_residual_independent Φ u
  have hcond := condExp_indep_eq hR.comap_le hm
    (comap_measurable (fun ω : H => ⟪r, ω⟫)).stronglyMeasurable hi
  have hmean : (∫ ω : H, ⟪r, ω⟫ ∂stdGaussian H) = 0 :=
    integral_strongDual_stdGaussian (innerSL ℝ r)
  rw [hmean] at hcond
  have hp : StronglyMeasurable[MeasurableSpace.comap Φ.adjoint inferInstance]
      (fun ω : H => ⟪c, Φ.adjoint ω⟫) :=
    ((innerSL ℝ c).continuous.measurable.comp (comap_measurable Φ.adjoint)).stronglyMeasurable
  have hRi : Integrable (fun ω : H => ⟪r, ω⟫) (stdGaussian H) :=
    (IsGaussian.hasGaussianLaw_id.map (innerSL ℝ r)).integrable
  have hpi : Integrable (fun ω : H => ⟪c, Φ.adjoint ω⟫) (stdGaussian H) :=
    (IsGaussian.hasGaussianLaw_id.map ((innerSL ℝ c).comp Φ.adjoint)).integrable
  have he : (fun ω : H => ⟪u, ω⟫) =
      (fun ω : H => ⟪r, ω⟫) + (fun ω => ⟪c, Φ.adjoint ω⟫) := by
    ext ω
    simp only [Pi.add_apply, r, inner_sub_left, ContinuousLinearMap.adjoint_inner_right,
      sub_add_cancel]
  rw [he]
  have hadd := condExp_add hRi hpi (MeasurableSpace.comap Φ.adjoint inferInstance)
  rw [condExp_of_stronglyMeasurable hm hp hpi] at hadd
  exact hadd.trans (by filter_upwards [hcond] with ω hω; simp only [Pi.add_apply, hω, zero_add, c])

end HilbertMetric.Correlation
