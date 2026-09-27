import GaloisForLFunctions.HTGeometry.ContinuousFrameGramBound
import GaloisForLFunctions.RHTower.PoleVanishingWeilTraceCertificate
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarStrictDomain

/-!
# The two-pole constrained Fourier Gram bound

Projecting an aperture plane wave onto both pole constraints gives its exact
Fourier evaluation vector on the constrained source space. The double Gram
bound retains all frequency correlations and both pole constraints together.
It applies to the complete source domain, with no finite-dimensional cutoff.
-/

open Complex MeasureTheory Set
open scoped InnerProduct FourierTransform BoundedContinuousFunction
noncomputable section
namespace RHTower

/-- The physical Hilbert space satisfying both exact pole moments. -/
def ccmPhysicalPolarKernel (a : SuzukiPositiveAperture) : Submodule ℂ SoninL2 :=
  (innerSL ℂ (ccmPolarL2Vector a (1/2))).ker ⊓
    (innerSL ℂ (ccmPolarL2Vector a (-1/2))).ker

private theorem physical_kernel_closed (a : SuzukiPositiveAperture) :
    IsClosed (ccmPhysicalPolarKernel a : Set SoninL2) := by
  change IsClosed ({f | inner ℂ (ccmPolarL2Vector a (1/2)) f = 0} ∩
    {f | inner ℂ (ccmPolarL2Vector a (-1/2)) f = 0})
  exact (isClosed_eq (continuous_const.inner continuous_id) continuous_const).inter
    (isClosed_eq (continuous_const.inner continuous_id) continuous_const)

instance ccmPhysicalPolarKernel_complete (a : SuzukiPositiveAperture) :
    CompleteSpace (ccmPhysicalPolarKernel a) :=
  (physical_kernel_closed a).completeSpace_coe

private theorem plane_wave_continuous (a : SuzukiPositiveAperture) :
    Continuous (planeWaveL2 a) := by
  let C := 4 * Real.pi ^ 2 * (2 * a.1 ^ 3 / 3)
  have ha : 0 < a.1 := a.2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have h : LipschitzWith ⟨Real.sqrt C, Real.sqrt_nonneg C⟩ (planeWaveL2 a) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, Real.dist_eq]
    change ‖planeWaveL2 a x - planeWaveL2 a y‖ ≤ Real.sqrt C * |x-y|
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hC, sq_abs]
    have hp := norm_sq_planeWaveL2_sub_le a x y
    dsimp only [C]
    nlinarith only [hp]
  exact h.continuous

private theorem norm_sq_plane_wave (a : SuzukiPositiveAperture) (ξ : ℝ) :
    ‖planeWaveL2 a ξ‖ ^ 2 = 2 * a.1 := by
  have h := norm_sq_poleResidualL2_eq_closedForm a ξ 0 0
  simpa [poleResidualL2, poleResidualClosedForm] using h

/-- The exact evaluation vector after simultaneous orthogonal removal of both poles. -/
def ccmPolarPlaneWave (a : SuzukiPositiveAperture) (ξ : ℝ) : SoninL2 :=
  (ccmPhysicalPolarKernel a).starProjection (planeWaveL2 a ξ)

theorem continuous_ccmPolarPlaneWave (a : SuzukiPositiveAperture) :
    Continuous (ccmPolarPlaneWave a) :=
  (ccmPhysicalPolarKernel a).starProjection.continuous.comp (plane_wave_continuous a)

theorem norm_sq_ccmPolarPlaneWave_le (a : SuzukiPositiveAperture) (ξ : ℝ) :
    ‖ccmPolarPlaneWave a ξ‖ ^ 2 ≤ 2 * a.1 := by
  have h := (ccmPhysicalPolarKernel a).norm_starProjection_apply_le (planeWaveL2 a ξ)
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (norm_sq_plane_wave a ξ)

/-- The whole constrained Fourier field is bounded independently of frequency. -/
def ccmPolarPlaneWaveFrame (a : SuzukiPositiveAperture) : ℝ →ᵇ SoninL2 :=
  BoundedContinuousFunction.ofNormedAddCommGroup (ccmPolarPlaneWave a)
    (continuous_ccmPolarPlaneWave a) (Real.sqrt (2*a.1)) (fun ξ => by
      exact (Real.le_sqrt (norm_nonneg _) (by linarith [a.2])).mpr
        (norm_sq_ccmPolarPlaneWave_le a ξ))

/-- Every actual constrained source pairs with the projected vector to give its Fourier value. -/
theorem inner_ccmPolarPlaneWave_eq_fourier (a : SuzukiPositiveAperture)
    (u : ccmPolarConstraintSubmodule a) (ξ : ℝ) :
    inner ℂ (ccmPolarPlaneWave a ξ) (ccmArchimedeanFormToAperture a u.1).1 =
      𝓕 ((ccmArchimedeanFormToAperture a u.1).1 : ℝ → ℂ) ξ := by
  have hu : (ccmArchimedeanFormToAperture a u.1).1 ∈ ccmPhysicalPolarKernel a := u.2
  rw [ccmPolarPlaneWave, Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr hu,
    fourier_eq_inner_planeWaveL2]

/-- Both pole corrections and every frequency cross term remain inside this Gram kernel. -/
def ccmPolarFourierGramKernel (a : SuzukiPositiveAperture) (ξ η : ℝ) : ℂ :=
  inner ℂ (ccmPolarPlaneWave a ξ) (ccmPolarPlaneWave a η)

def ccmPolarFourierGramEnergy (a : SuzukiPositiveAperture) (μ : Measure ℝ) : ℝ :=
  ∫ ξ, ∫ η, ‖ccmPolarFourierGramKernel a ξ η‖ ^ 2 ∂μ ∂μ

theorem ccmPolarFourierGramEnergy_nonneg (a : SuzukiPositiveAperture) (μ : Measure ℝ) :
    0 ≤ ccmPolarFourierGramEnergy a μ :=
  integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _

/-- A coefficient-uniform Fourier concentration bound on the complete constrained form domain. -/
theorem ccmPolarFourier_debt_le_gram (a : SuzukiPositiveAperture)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (u : ccmPolarConstraintSubmodule a) :
    (∫ ξ, ‖𝓕 ((ccmArchimedeanFormToAperture a u.1).1 : ℝ → ℂ) ξ‖ ^ 2 ∂μ) ≤
      Real.sqrt (ccmPolarFourierGramEnergy a μ) * ‖ccmArchimedeanFormToAperture a u.1‖ ^ 2 := by
  have h := HTGeometry.continuousFrame_analysis_le_gram μ (ccmPolarPlaneWaveFrame a)
    (ccmArchimedeanFormToAperture a u.1).1
  change (∫ ξ, ‖inner ℂ (ccmPolarPlaneWave a ξ)
      (ccmArchimedeanFormToAperture a u.1).1‖ ^ 2 ∂μ) ≤ _ at h
  simpa only [inner_ccmPolarPlaneWave_eq_fourier, HTGeometry.continuousFrameGramEnergy,
    ccmPolarFourierGramEnergy, ccmPolarFourierGramKernel, ccmPolarPlaneWaveFrame,
    BoundedContinuousFunction.coe_ofNormedAddCommGroup, Submodule.norm_coe] using h

/-- The correlation ceiling is no larger than the exact constrained diagonal trace. -/
theorem ccmPolarFourier_gram_le_trace (a : SuzukiPositiveAperture)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Real.sqrt (ccmPolarFourierGramEnergy a μ) ≤
      ∫ ξ, ‖ccmPolarPlaneWave a ξ‖ ^ 2 ∂μ :=
  HTGeometry.continuousFrame_gram_le_trace μ (ccmPolarPlaneWaveFrame a)

end RHTower
