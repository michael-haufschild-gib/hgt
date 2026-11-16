import GaloisForLFunctions.HTGeometry.BoundedKernelReindexing
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# Actual Gaussian realization of finite complex kernels

A finite positive semidefinite kernel has a finite-dimensional Gram Hilbert
space, even when its Gram matrix is singular. Standard Gaussian measure on
its underlying real space realizes all complex quadratures jointly, with
their covariance given exactly by the real part of the phased kernel.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ComplexConjugate
namespace GaloisForLFunctions.HTGeometry
variable {X : Type*} [Finite X] (K : X → X → ℂ) [Fact (IsPSDKernel K)]

/-- Finite kernels have finite-dimensional completed Gram realizations, including singular kernels. -/
instance finiteDimensional_kernelHilbert : FiniteDimensional ℂ (KernelHilbert K) := by
  let S := Submodule.span ℂ (Set.range (KernelHilbert.vector K))
  letI : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  apply FiniteDimensional.of_surjective S.subtype
  intro x
  refine ⟨⟨x, ?_⟩, rfl⟩
  change x ∈ (S : Set (KernelHilbert K))
  rw [← S.closed_of_finiteDimensional.closure_eq]
  exact KernelHilbert.dense_span_vectors K x

local instance kernelHilbert_measurableSpace : MeasurableSpace (KernelHilbert K) :=
  borel (KernelHilbert K)

local instance kernelHilbert_borelSpace : BorelSpace (KernelHilbert K) := ⟨rfl⟩

local instance kernelHilbert_realInner : InnerProductSpace ℝ (KernelHilbert K) :=
  InnerProductSpace.complexToReal

local instance kernelHilbert_realFinite : FiniteDimensional ℝ (KernelHilbert K) :=
  FiniteDimensional.trans ℝ ℂ (KernelHilbert K)

/-- Gaussian probability measure on the actual Gram realization of the finite kernel. -/
def finiteKernelGaussianMeasure : Measure (KernelHilbert K) :=
  stdGaussian (KernelHilbert K)

instance finiteKernelGaussianMeasure_probability : IsProbabilityMeasure (finiteKernelGaussianMeasure K) :=
  inferInstanceAs (IsProbabilityMeasure (stdGaussian (KernelHilbert K)))

instance finiteKernelGaussianMeasure_isGaussian : IsGaussian (finiteKernelGaussianMeasure K) :=
  inferInstanceAs (IsGaussian (stdGaussian (KernelHilbert K)))

/-- A real quadrature at an arbitrary complex phase and kernel index. -/
def finiteKernelQuadrature (p : ℂ × X) (ω : KernelHilbert K) : ℝ :=
  ⟪p.1 • KernelHilbert.vector K p.2, ω⟫_ℝ

/-- Every finite collection of phased quadratures has a genuine joint Gaussian law. -/
theorem finiteKernelQuadrature_isGaussianProcess :
    IsGaussianProcess (finiteKernelQuadrature K) (finiteKernelGaussianMeasure K) where
  hasGaussianLaw I := by
    exact IsGaussian.hasGaussianLaw_id.map
      (ContinuousLinearMap.pi (fun p : I => innerSL ℝ (p.val.1 • KernelHilbert.vector K p.val.2)))

/-- Exact covariance of arbitrary quadratures, retaining the imaginary kernel data. -/
theorem finiteKernelQuadrature_covariance (a b : ℂ) (x y : X) :
    cov[finiteKernelQuadrature K (a, x), finiteKernelQuadrature K (b, y);
      finiteKernelGaussianMeasure K] = (conj a * b * K y x).re := by
  change cov[fun ω => ⟪a • KernelHilbert.vector K x, ω⟫_ℝ,
    fun ω => ⟪b • KernelHilbert.vector K y, ω⟫_ℝ; stdGaussian (KernelHilbert K)] = _
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, innerSL_apply_apply]
  rw [real_inner_eq_re_inner ℂ, inner_smul_left, inner_smul_right, KernelHilbert.inner_vector]
  change (conj a * (b * K y x)).re = (conj a * b * K y x).re
  rw [mul_assoc]

end GaloisForLFunctions.HTGeometry
