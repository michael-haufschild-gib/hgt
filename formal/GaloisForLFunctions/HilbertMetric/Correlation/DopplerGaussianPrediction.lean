import GaloisForLFunctions.HilbertMetric.Correlation.DopplerFinitePrediction
import GaloisForLFunctions.HilbertMetric.Correlation.FiniteKernelGaussian
import GaloisForLFunctions.HilbertMetric.Correlation.ComplexGaussianPrediction
import GaloisForLFunctions.HilbertMetric.Correlation.ProperKernelGaussian

/-!
# Gaussian pilot prediction with the actual Doppler covariance

The finite noisy Doppler kernel defines an actual Gaussian probability law.
All phased channel coordinates are jointly Gaussian with the prescribed
covariance. The singular Gram predictor is their conditional mean given the
complete complex pilot vector, including repeated times and zero noise.
-/

noncomputable section
open MeasureTheory ProbabilityTheory GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace ComplexConjugate
namespace HilbertMetric.Correlation
variable {ι : Type*} [Fintype ι]
variable (w : ι → NNReal) (mean : ι → ℝ) (variance : ι → NNReal)
  {n : ℕ} (time : Fin n → ℝ) (target : ℝ) (noise : Fin n → NNReal)

local notation "K" => dopplerObservationKernel w mean variance time target noise
local notation "H" => KernelHilbert K

local instance : MeasurableSpace H := borel H
local instance : BorelSpace H := ⟨rfl⟩
local instance : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
local instance : FiniteDimensional ℝ H := FiniteDimensional.trans ℝ ℂ H

/-- The noisy finite Doppler model is a genuine Gaussian process of all quadratures. -/
theorem dopplerGaussian_isGaussianProcess :
    IsGaussianProcess (finiteKernelQuadrature K) (finiteKernelGaussianMeasure K) :=
  finiteKernelQuadrature_isGaussianProcess K

/-- Exact Doppler-and-noise covariance, including the imaginary cross-channel data. -/
theorem dopplerGaussian_quadrature_covariance (a b : ℂ) (i j : Option (Fin n)) :
    cov[finiteKernelQuadrature K (a, i), finiteKernelQuadrature K (b, j);
      finiteKernelGaussianMeasure K] =
      (conj a * b * (dopplerClusterKernel w mean variance
        (j.elim target time - i.elim target time) +
          if j = i then ((j.elim (0 : NNReal) noise : NNReal) : ℂ) else 0)).re :=
  finiteKernelQuadrature_covariance K a b i j

/-- The existing Doppler Gram coefficients give the actual Gaussian conditional mean
of every target quadrature, with no nonsingularity premise. -/
theorem dopplerGaussian_conditional_mean_quadrature (a : ℂ) :
    (finiteKernelGaussianMeasure K)[finiteKernelQuadrature K (a, none) |
      MeasurableSpace.comap (dopplerObservationMap w mean variance time target noise).adjoint
        inferInstance] =ᵐ[finiteKernelGaussianMeasure K]
      fun ω => (⟪a • dopplerPredictionCoefficients w mean variance time target noise,
        (dopplerObservationMap w mean variance time target noise).adjoint ω⟫_ℂ).re :=
  complexGaussian_conditional_mean_quadrature
    (dopplerObservationMap w mean variance time target noise) (KernelHilbert.vector K none) a

/-- The physical complex pilot vector, with the proper Gaussian normalization. -/
def dopplerGaussianPilots (ω : H) : Fin n → ℂ :=
  properPilotReadout ((dopplerObservationMap w mean variance time target noise).adjoint ω)

/-- Each physical pilot is precisely the corresponding coordinate of the Gaussian channel. -/
theorem dopplerGaussianPilot_eq_signal (i : Fin n) (ω : H) :
    dopplerGaussianPilots w mean variance time target noise ω i =
      finiteKernelSignal K (some i) ω := by
  have h := ContinuousLinearMap.adjoint_inner_right
    (dopplerObservationMap w mean variance time target noise) (EuclideanSpace.single i 1) ω
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, dopplerObservationMap_single] at h
  change (Real.sqrt 2)⁻¹ • conj
    ((dopplerObservationMap w mean variance time target noise).adjoint ω i) =
      (Real.sqrt 2)⁻¹ • conj (⟪KernelHilbert.vector K (some i), ω⟫_ℂ)
  rw [h]

/-- The complex target and pilots are jointly Gaussian under the constructed probability law. -/
theorem dopplerGaussianSignal_isGaussianProcess :
    IsGaussianProcess (finiteKernelSignal K) (finiteKernelGaussianMeasure K) :=
  finiteKernelSignal_isGaussianProcess K

/-- The complex covariance has exactly the Doppler-and-noise normalization; its pseudo-covariance is zero. -/
theorem dopplerGaussianSignal_covariance (i j : Option (Fin n)) :
    complexSignalCovariance (finiteKernelGaussianMeasure K)
      (finiteKernelSignal K i) (finiteKernelSignal K j) =
        dopplerClusterKernel w mean variance (i.elim target time - j.elim target time) +
          (if i = j then ((i.elim (0 : NNReal) noise : NNReal) : ℂ) else 0) ∧
    complexSignalPseudoCovariance (finiteKernelGaussianMeasure K)
      (finiteKernelSignal K i) (finiteKernelSignal K j) = 0 :=
  finiteKernelSignal_covariance_and_properness K i j

/-- Exact complex Gaussian prediction from the actual physical pilot vector. Repeated sampling
times and zero noise are allowed; no inverse-covariance premise is hidden in the statement. -/
theorem dopplerGaussian_conditional_mean :
    (finiteKernelGaussianMeasure K)[finiteKernelSignal K none |
      MeasurableSpace.comap (dopplerGaussianPilots w mean variance time target noise)
        inferInstance] =ᵐ[finiteKernelGaussianMeasure K]
      fun ω => ∑ i, dopplerPredictionCoefficients w mean variance time target noise i *
        dopplerGaussianPilots w mean variance time target noise ω i := by
  have h := complexGaussian_conditional_mean_proper
    (dopplerObservationMap w mean variance time target noise) (KernelHilbert.vector K none)
  change (finiteKernelGaussianMeasure K)[finiteKernelSignal K none |
      MeasurableSpace.comap (dopplerObservationMap w mean variance time target noise).adjoint
        inferInstance] =ᵐ[finiteKernelGaussianMeasure K]
      fun ω => (Real.sqrt 2)⁻¹ • conj
        (⟪dopplerPredictionCoefficients w mean variance time target noise,
          (dopplerObservationMap w mean variance time target noise).adjoint ω⟫_ℂ) at h
  simp_rw [properPilotReadout_prediction] at h
  have hm : MeasurableSpace.comap
      (dopplerGaussianPilots w mean variance time target noise) inferInstance =
      MeasurableSpace.comap
        (dopplerObservationMap w mean variance time target noise).adjoint inferInstance :=
    properPilotReadout_comap (dopplerObservationMap w mean variance time target noise).adjoint
  rw [hm]
  exact h

end HilbertMetric.Correlation
