import GaloisForLFunctions.HilbertMetric.Correlation.FiniteKernelGaussian

/-!
# Proper complex Gaussian signals with prescribed kernel

Dividing the conjugate Gram coordinate by `√2` gives the complex covariance
`K`, rather than `2K`. The real and imaginary covariance blocks are explicit;
the complex covariance is `K` and the pseudo-covariance vanishes.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ComplexConjugate
namespace GaloisForLFunctions.HTGeometry

/-- Complex covariance assembled from the four real covariance blocks. -/
def complexSignalCovariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z W : Ω → ℂ) : ℂ :=
  ⟨cov[fun ω => (Z ω).re, fun ω => (W ω).re; μ] +
      cov[fun ω => (Z ω).im, fun ω => (W ω).im; μ],
    cov[fun ω => (Z ω).im, fun ω => (W ω).re; μ] -
      cov[fun ω => (Z ω).re, fun ω => (W ω).im; μ]⟩

/-- Complex pseudo-covariance, whose vanishing expresses properness. -/
def complexSignalPseudoCovariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z W : Ω → ℂ) : ℂ :=
  ⟨cov[fun ω => (Z ω).re, fun ω => (W ω).re; μ] -
      cov[fun ω => (Z ω).im, fun ω => (W ω).im; μ],
    cov[fun ω => (Z ω).im, fun ω => (W ω).re; μ] +
      cov[fun ω => (Z ω).re, fun ω => (W ω).im; μ]⟩

variable {X : Type*} [Finite X] (K : X → X → ℂ) [Fact (IsPSDKernel K)]

local instance : MeasurableSpace (KernelHilbert K) := borel (KernelHilbert K)
local instance : BorelSpace (KernelHilbert K) := ⟨rfl⟩
local instance : InnerProductSpace ℝ (KernelHilbert K) := InnerProductSpace.complexToReal

/-- The normalized complex signal as a real continuous linear map. -/
def finiteKernelSignalMap (x : X) : KernelHilbert K →L[ℝ] ℂ :=
  (Real.sqrt 2)⁻¹ • ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
    ((innerSL ℂ (KernelHilbert.vector K x)).restrictScalars ℝ))

/-- A proper complex signal with the exact prescribed covariance normalization. -/
def finiteKernelSignal (x : X) (ω : KernelHilbert K) : ℂ := finiteKernelSignalMap K x ω

theorem finiteKernelSignal_isGaussianProcess :
    IsGaussianProcess (finiteKernelSignal K) (finiteKernelGaussianMeasure K) where
  hasGaussianLaw I := IsGaussian.hasGaussianLaw_id.map
    (ContinuousLinearMap.pi (fun x : I => finiteKernelSignalMap K x))

theorem finiteKernelSignal_mean (x : X) :
    ∫ ω, finiteKernelSignal K x ω ∂finiteKernelGaussianMeasure K = 0 := by
  change ∫ ω, finiteKernelSignalMap K x ω ∂stdGaussian (KernelHilbert K) = 0
  simpa only [integral_id_stdGaussian, map_zero] using
    (finiteKernelSignalMap K x).integral_comp_id_comm
      (μ := stdGaussian (KernelHilbert K)) IsGaussian.integrable_id

omit [Finite X] in
theorem finiteKernelSignal_re (x : X) (ω : KernelHilbert K) :
    (finiteKernelSignal K x ω).re = (Real.sqrt 2)⁻¹ * finiteKernelQuadrature K (1, x) ω := by
  change (Complex.ofReal ((Real.sqrt 2)⁻¹) * conj (⟪KernelHilbert.vector K x, ω⟫_ℂ)).re = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.conj_re, finiteKernelQuadrature, one_smul, real_inner_eq_re_inner ℂ]
  rfl

omit [Finite X] in
theorem finiteKernelSignal_im (x : X) (ω : KernelHilbert K) :
    (finiteKernelSignal K x ω).im = -(Real.sqrt 2)⁻¹ * finiteKernelQuadrature K (Complex.I, x) ω := by
  change (Complex.ofReal ((Real.sqrt 2)⁻¹) * conj (⟪KernelHilbert.vector K x, ω⟫_ℂ)).im = _
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.conj_im, finiteKernelQuadrature, real_inner_eq_re_inner ℂ, inner_smul_left]
  change (Real.sqrt 2)⁻¹ * -(⟪KernelHilbert.vector K x, ω⟫_ℂ).im =
    -(Real.sqrt 2)⁻¹ * (conj Complex.I * ⟪KernelHilbert.vector K x, ω⟫_ℂ).re
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    zero_mul, neg_mul, one_mul, zero_sub, neg_neg]
  ring

private theorem gaussian_scale_square : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
  rw [← pow_two, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- All four covariance blocks of the actual real and imaginary signal coordinates. -/
theorem finiteKernelSignal_covariance_blocks (x y : X) :
    cov[fun ω => (finiteKernelSignal K x ω).re, fun ω => (finiteKernelSignal K y ω).re;
      finiteKernelGaussianMeasure K] = (K y x).re / 2 ∧
    cov[fun ω => (finiteKernelSignal K x ω).im, fun ω => (finiteKernelSignal K y ω).im;
      finiteKernelGaussianMeasure K] = (K y x).re / 2 ∧
    cov[fun ω => (finiteKernelSignal K x ω).re, fun ω => (finiteKernelSignal K y ω).im;
      finiteKernelGaussianMeasure K] = (K y x).im / 2 ∧
    cov[fun ω => (finiteKernelSignal K x ω).im, fun ω => (finiteKernelSignal K y ω).re;
      finiteKernelGaussianMeasure K] = -(K y x).im / 2 := by
  simp_rw [finiteKernelSignal_re, finiteKernelSignal_im, covariance_const_mul_left,
    covariance_const_mul_right, finiteKernelQuadrature_covariance]
  simp only [map_one, one_mul, mul_one, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul, mul_one,
    neg_mul, neg_neg, zero_sub, add_zero, sub_zero]
  have hs := gaussian_scale_square
  constructor
  · linear_combination (K y x).re * hs
  constructor
  · linear_combination (K y x).re * hs
  constructor
  · linear_combination (K y x).im * hs
  · linear_combination -(K y x).im * hs

/-- The normalized signals have complex covariance exactly `K` and zero pseudo-covariance. -/
theorem finiteKernelSignal_covariance_and_properness (x y : X) :
    complexSignalCovariance (finiteKernelGaussianMeasure K)
      (finiteKernelSignal K x) (finiteKernelSignal K y) = K x y ∧
    complexSignalPseudoCovariance (finiteKernelGaussianMeasure K)
      (finiteKernelSignal K x) (finiteKernelSignal K y) = 0 := by
  obtain ⟨hrr, hii, hri, hir⟩ := finiteKernelSignal_covariance_blocks K x y
  have hsym := (Fact.out : IsPSDKernel K).conj_symm y x
  constructor
  · rw [complexSignalCovariance, hrr, hii, hri, hir, ← hsym]
    apply Complex.ext <;> simp only [Complex.conj_re,
      Complex.conj_im] <;> ring
  · rw [complexSignalPseudoCovariance, hrr, hii, hri, hir]
    apply Complex.ext <;> simp only [Complex.zero_re,
      Complex.zero_im] <;> ring

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.finiteKernelSignal_mean
