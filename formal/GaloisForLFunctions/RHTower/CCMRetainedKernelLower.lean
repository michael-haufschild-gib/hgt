import GaloisForLFunctions.RHTower.CCMApertureCorrelationKernel
import GaloisForLFunctions.RHTower.CCMPositiveFrequencyMeasure

/-!
# A physical signed-kernel lower bound for the complete source

The negative frequency weight and retained positive window are transformed
together. Their physical cancellation precedes the modulus. The resulting
bound holds for every vector of the complete form domain and every retention
fraction, without a finite-dimensional cutoff or a covariance Hilbert norm.
-/

open Complex MeasureTheory Set
open scoped FourierTransform
noncomputable section
namespace RHTower

def ccmRetainedSignedFrequencyWeight (a : SuzukiPositiveAperture) (α R θ ξ : ℝ) : ℝ :=
  ccmActualSourceNegativeWeight a α ξ - θ * ccmPositiveFrequencyWeight a α R ξ

theorem continuous_ccmRetainedSignedFrequencyWeight
    (a : SuzukiPositiveAperture) (α R θ : ℝ) :
    Continuous (ccmRetainedSignedFrequencyWeight a α R θ) :=
  (continuous_ccmActualSourceNegativeWeight a α).sub
    (continuous_const.mul (continuous_ccmPositiveFrequencyWeight a α R))

theorem integrable_ccmRetainedSignedFrequencyWeight
    (a : SuzukiPositiveAperture) (α R θ : ℝ) :
    Integrable (fun ξ => (ccmRetainedSignedFrequencyWeight a α R θ ξ : ℂ)) :=
  ((integrable_ccmActualSourceNegativeWeight a α).sub
    ((integrable_ccmPositiveFrequencyWeight a α R).const_mul θ)).ofReal

theorem hasCompactSupport_ccmRetainedSignedFrequencyWeight
    (a : SuzukiPositiveAperture) (α R θ : ℝ) :
    HasCompactSupport (ccmRetainedSignedFrequencyWeight a α R θ) :=
  (hasCompactSupport_ccmActualSourceNegativeWeight a α).sub
    (hasCompactSupport_ccmPositiveFrequencyWeight a α R).mul_left

/-- Both frequency signs remain inside the physical kernel. -/
def ccmRetainedPhysicalKernel (a : SuzukiPositiveAperture) (α R θ h : ℝ) : ℂ :=
  𝓕⁻ (fun ξ => (ccmRetainedSignedFrequencyWeight a α R θ ξ : ℂ)) h

def ccmRetainedKernelCeiling (a : SuzukiPositiveAperture) (α R θ : ℝ) : ℝ :=
  ccmApertureSignedKernelMass a (fun ξ => (ccmRetainedSignedFrequencyWeight a α R θ ξ : ℂ))

theorem ccmRetainedKernelCeiling_nonneg (a : SuzukiPositiveAperture) (α R θ : ℝ) :
    0 ≤ ccmRetainedKernelCeiling a α R θ := ccmApertureSignedKernelMass_nonneg a _

/-- Exact retained spectral pairing, with the full form-domain representative. -/
theorem ccmRetainedSignedFrequency_pairing (a : SuzukiPositiveAperture) (α R θ : ℝ)
    (u : CCMArchimedeanFormDomain a) :
    (∫ ξ, (ccmRetainedSignedFrequencyWeight a α R θ ξ : ℂ) *
      ccmApertureFourierDensity a (ccmArchimedeanFormToAperture a u) ξ) =
    (((∫ ξ, ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 ∂ccmActualSourceNegativeMeasure a α) -
      θ * (∫ ξ, ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 ∂ccmPositiveFrequencyMeasure a α R) : ℝ) : ℂ) := by
  let f := ccmArchimedeanFormToAperture a u
  let φ : ℝ → ℝ := fun ξ => ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ^ 2
  have hφ : Continuous φ := by
    have h := Complex.continuous_re.comp (continuous_ccmApertureFourierDensity a f)
    exact h
  have hN : Integrable (fun ξ => ccmActualSourceNegativeWeight a α ξ * φ ξ) :=
    ((continuous_ccmActualSourceNegativeWeight a α).mul hφ).integrable_of_hasCompactSupport
      (hasCompactSupport_ccmActualSourceNegativeWeight a α).mul_right
  have hP : Integrable (fun ξ => ccmPositiveFrequencyWeight a α R ξ * φ ξ) :=
    ((continuous_ccmPositiveFrequencyWeight a α R).mul hφ).integrable_of_hasCompactSupport
      (hasCompactSupport_ccmPositiveFrequencyWeight a α R).mul_right
  have hNrep : (∫ ξ, ccmActualSourceNegativeWeight a α ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) =
      ∫ ξ, ccmActualSourceNegativeWeight a α ξ * φ ξ := by
    apply integral_congr_ae
    filter_upwards [ccmFormDomain_ae_eq_fourier a u] with ξ hξ
    rw [hξ]
  have hPrep : (∫ ξ, ccmPositiveFrequencyWeight a α R ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) =
      ∫ ξ, ccmPositiveFrequencyWeight a α R ξ * φ ξ := by
    apply integral_congr_ae
    filter_upwards [ccmFormDomain_ae_eq_fourier a u] with ξ hξ
    rw [hξ]
  rw [ccmNegativeFrequency_integral, ccmPositiveFrequency_integral, hNrep, hPrep]
  calc
    _ = ∫ ξ, ((ccmActualSourceNegativeWeight a α ξ * φ ξ -
        θ * (ccmPositiveFrequencyWeight a α R ξ * φ ξ) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with ξ
      dsimp only [ccmRetainedSignedFrequencyWeight, ccmApertureFourierDensity, φ, f]
      push_cast
      ring
    _ = _ := by
      rw [integral_complex_ofReal, integral_sub hN (hP.const_mul θ), integral_const_mul]

/-- Full retained debt is bounded on every source by an independent physical kernel integral. -/
theorem ccmRetained_debt_abs_le_kernel
    (a : SuzukiPositiveAperture) (α R θ : ℝ) (u : CCMArchimedeanFormDomain a) :
    |(∫ ξ, ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 ∂ccmActualSourceNegativeMeasure a α) -
      θ * (∫ ξ, ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 ∂ccmPositiveFrequencyMeasure a α R)| ≤
        ccmRetainedKernelCeiling a α R θ * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
  have h := norm_integral_weight_mul_ccmApertureFourierDensity_le a
    (ccmArchimedeanFormToAperture a u)
    (fun ξ => (ccmRetainedSignedFrequencyWeight a α R θ ξ : ℂ))
    (integrable_ccmRetainedSignedFrequencyWeight a α R θ)
  rw [ccmRetainedSignedFrequency_pairing, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- The entire actual source, for all coefficient orders and every retained fraction. -/
theorem ccmRestrictedWeilSource_ge_retainedKernel
    (a : SuzukiPositiveAperture) (α R : ℝ) (θ : Icc (0 : ℝ) 1)
    (u : CCMArchimedeanFormDomain a) :
    (α - ccmRetainedKernelCeiling a α R θ.1) * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u := by
  have hsource := ccmRestrictedWeilSource_ge_retainedPositiveWindow a α R θ u
  have hdebt := (le_abs_self _).trans (ccmRetained_debt_abs_le_kernel a α R θ.1 u)
  nlinarith only [hsource, hdebt]

end RHTower
