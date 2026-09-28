import GaloisForLFunctions.HTGeometry.L2FrameCovariance
import GaloisForLFunctions.RHTower.CCMPositiveFrequencyMeasure

/-!
# An independent positive-frequency saving in the actual source Gram ceiling

A compact positive-frequency window is subtracted from negative-frequency
covariance before taking the Hilbert norm. The retained fraction is chosen
from the actual cross Gram, independently of source coefficients or degree.
The resulting ceiling never exceeds the previous negative-only ceiling.
Its exact squared saving includes every negative-positive frequency pair.
-/

open Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open scoped InnerProduct FourierTransform
noncomputable section
namespace RHTower

def ccmNegativeFrequencyCovariance (a : SuzukiPositiveAperture) (α : ℝ) : L2DensitySpace :=
  l2FrameCovariance (ccmActualSourceNegativeMeasure a α) (ccmPolarPlaneWaveFrame a)

def ccmPositiveFrequencyCovariance (a : SuzukiPositiveAperture) (α R : ℝ) : L2DensitySpace :=
  l2FrameCovariance (ccmPositiveFrequencyMeasure a α R) (ccmPolarPlaneWaveFrame a)

/-- The complete negative-positive frequency interaction after simultaneous removal of both poles. -/
def ccmPositiveFrequencyCrossGram (a : SuzukiPositiveAperture) (α R : ℝ) : ℝ :=
  l2FrameCrossGram (ccmActualSourceNegativeMeasure a α)
    (ccmPositiveFrequencyMeasure a α R) (ccmPolarPlaneWaveFrame a)

theorem ccmPositiveFrequencyCrossGram_nonneg (a : SuzukiPositiveAperture) (α R : ℝ) :
    0 ≤ ccmPositiveFrequencyCrossGram a α R := l2FrameCrossGram_nonneg _ _ _

theorem ccmFrequencyCovariance_inner_re (a : SuzukiPositiveAperture) (α R : ℝ) :
    (inner ℂ (ccmNegativeFrequencyCovariance a α)
      (ccmPositiveFrequencyCovariance a α R)).re = ccmPositiveFrequencyCrossGram a α R :=
  l2FrameCovariance_inner_re _ _ _

theorem norm_ccmNegativeFrequencyCovariance_sq (a : SuzukiPositiveAperture) (α : ℝ) :
    ‖ccmNegativeFrequencyCovariance a α‖ ^ 2 = ccmActualSourceGramCeiling a α ^ 2 := by
  rw [ccmNegativeFrequencyCovariance, norm_l2FrameCovariance_sq,
    ccmActualSourceGramCeiling, Real.sq_sqrt (ccmPolarFourierGramEnergy_nonneg a _)]
  rfl

/-- The optimal retained fraction on the interval `[0,1]`, with zero window handled by division at zero. -/
def ccmPositiveFrequencyRetention (a : SuzukiPositiveAperture) (α R : ℝ) : ℝ :=
  min 1 (ccmPositiveFrequencyCrossGram a α R / ‖ccmPositiveFrequencyCovariance a α R‖ ^ 2)

theorem ccmPositiveFrequencyRetention_bounds (a : SuzukiPositiveAperture) (α R : ℝ) :
    0 ≤ ccmPositiveFrequencyRetention a α R ∧ ccmPositiveFrequencyRetention a α R ≤ 1 := by
  exact ⟨le_min (by norm_num) (div_nonneg (ccmPositiveFrequencyCrossGram_nonneg a α R)
    (sq_nonneg _)), min_le_left _ _⟩

private theorem retained_energy_le_cross (a : SuzukiPositiveAperture) (α R : ℝ) :
    ccmPositiveFrequencyRetention a α R * ‖ccmPositiveFrequencyCovariance a α R‖ ^ 2 ≤
      ccmPositiveFrequencyCrossGram a α R := by
  by_cases hz : ‖ccmPositiveFrequencyCovariance a α R‖ ^ 2 = 0
  · simpa only [hz, mul_zero] using ccmPositiveFrequencyCrossGram_nonneg a α R
  · calc
      _ ≤ (ccmPositiveFrequencyCrossGram a α R /
          ‖ccmPositiveFrequencyCovariance a α R‖ ^ 2) *
          ‖ccmPositiveFrequencyCovariance a α R‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
      _ = _ := div_mul_cancel₀ _ hz

/-- The signed covariance ceiling keeps the positive window inside the norm. -/
def ccmPositiveFrequencyGramCeiling (a : SuzukiPositiveAperture) (α R : ℝ) : ℝ :=
  ‖ccmNegativeFrequencyCovariance a α -
    (ccmPositiveFrequencyRetention a α R : ℂ) • ccmPositiveFrequencyCovariance a α R‖

/-- The exact gain, including its quadratic positive-window cost. -/
def ccmPositiveFrequencyGramSaving (a : SuzukiPositiveAperture) (α R : ℝ) : ℝ :=
  2 * ccmPositiveFrequencyRetention a α R * ccmPositiveFrequencyCrossGram a α R -
    ccmPositiveFrequencyRetention a α R ^ 2 * ‖ccmPositiveFrequencyCovariance a α R‖ ^ 2

theorem ccmPositiveFrequencyGramSaving_ge_cross (a : SuzukiPositiveAperture) (α R : ℝ) :
    ccmPositiveFrequencyRetention a α R * ccmPositiveFrequencyCrossGram a α R ≤
      ccmPositiveFrequencyGramSaving a α R := by
  have h := mul_le_mul_of_nonneg_left (retained_energy_le_cross a α R)
    (ccmPositiveFrequencyRetention_bounds a α R).1
  unfold ccmPositiveFrequencyGramSaving
  nlinarith only [h]

theorem ccmPositiveFrequencyGramSaving_nonneg (a : SuzukiPositiveAperture) (α R : ℝ) :
    0 ≤ ccmPositiveFrequencyGramSaving a α R :=
  (mul_nonneg (ccmPositiveFrequencyRetention_bounds a α R).1
    (ccmPositiveFrequencyCrossGram_nonneg a α R)).trans
      (ccmPositiveFrequencyGramSaving_ge_cross a α R)

/-- Every negative-positive cross term appears with its exact favorable sign. -/
theorem ccmPositiveFrequencyGramCeiling_sq_add_saving (a : SuzukiPositiveAperture) (α R : ℝ) :
    ccmPositiveFrequencyGramCeiling a α R ^ 2 + ccmPositiveFrequencyGramSaving a α R =
      ccmActualSourceGramCeiling a α ^ 2 := by
  have h := norm_l2FrameCovariance_sub_sq (ccmActualSourceNegativeMeasure a α)
    (ccmPositiveFrequencyMeasure a α R) (ccmPolarPlaneWaveFrame a)
    (ccmPositiveFrequencyRetention a α R)
  rw [← norm_l2FrameCovariance_sq, ← norm_l2FrameCovariance_sq] at h
  change ccmPositiveFrequencyGramCeiling a α R ^ 2 =
    ‖ccmNegativeFrequencyCovariance a α‖ ^ 2 -
      2 * ccmPositiveFrequencyRetention a α R * ccmPositiveFrequencyCrossGram a α R +
      ccmPositiveFrequencyRetention a α R ^ 2 * ‖ccmPositiveFrequencyCovariance a α R‖ ^ 2 at h
  rw [norm_ccmNegativeFrequencyCovariance_sq] at h
  unfold ccmPositiveFrequencyGramSaving
  linarith only [h]

/-- This improvement is independent of the source and can never worsen the old Gram bound. -/
theorem ccmPositiveFrequencyGramCeiling_le_old (a : SuzukiPositiveAperture) (α R : ℝ) :
    ccmPositiveFrequencyGramCeiling a α R ≤ ccmActualSourceGramCeiling a α := by
  apply (sq_le_sq₀ (norm_nonneg _) (ccmActualSourceGramCeiling_nonneg a α)).mp
  change ccmPositiveFrequencyGramCeiling a α R ^ 2 ≤ ccmActualSourceGramCeiling a α ^ 2
  have h := ccmPositiveFrequencyGramCeiling_sq_add_saving a α R
  have hs := ccmPositiveFrequencyGramSaving_nonneg a α R
  linarith only [h,hs]

/-- The literal full source retains positive-frequency cancellation uniformly on the whole domain. -/
theorem ccmRestrictedWeilSource_ge_positiveFrequencyGram
    (a : SuzukiPositiveAperture) (α R : ℝ) (u : ccmPolarConstraintSubmodule a) :
    (α - ccmPositiveFrequencyGramCeiling a α R) * ‖ccmArchimedeanFormToAperture a u.1‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u.1 := by
  let f := ccmArchimedeanFormToAperture a u.1
  let φ : ℝ → ℝ := fun ξ => ‖(u.1.1 : ℝ → ℂ) ξ‖ ^ 2
  have hsame : ∀ᵐ ξ, ‖inner ℂ (ccmPolarPlaneWaveFrame a ξ) f.1‖ ^ 2 = φ ξ := by
    filter_upwards [ccmFormDomain_ae_eq_fourier a u.1] with ξ hξ
    change ‖inner ℂ (ccmPolarPlaneWave a ξ) f.1‖ ^ 2 = _
    rw [inner_ccmPolarPlaneWave_eq_fourier a u]
    dsimp only [φ, f]
    rw [hξ]
  have hN : (∫ ξ, ‖inner ℂ (ccmPolarPlaneWaveFrame a ξ) f.1‖ ^ 2
      ∂ccmActualSourceNegativeMeasure a α) = ∫ ξ, φ ξ ∂ccmActualSourceNegativeMeasure a α := by
    rw [ccmNegativeFrequency_integral, ccmNegativeFrequency_integral]
    apply integral_congr_ae
    filter_upwards [hsame] with ξ hξ
    rw [hξ]
  have hP : (∫ ξ, ‖inner ℂ (ccmPolarPlaneWaveFrame a ξ) f.1‖ ^ 2
      ∂ccmPositiveFrequencyMeasure a α R) = ∫ ξ, φ ξ ∂ccmPositiveFrequencyMeasure a α R := by
    rw [ccmPositiveFrequency_integral, ccmPositiveFrequency_integral]
    apply integral_congr_ae
    filter_upwards [hsame] with ξ hξ
    rw [hξ]
  have hb := abs_l2Frame_difference_le (ccmActualSourceNegativeMeasure a α)
    (ccmPositiveFrequencyMeasure a α R) (ccmPolarPlaneWaveFrame a)
    (ccmPositiveFrequencyRetention a α R) f.1
  rw [hN,hP] at hb
  have hdebt := (le_abs_self _).trans hb
  change (∫ ξ, φ ξ ∂ccmActualSourceNegativeMeasure a α) -
    ccmPositiveFrequencyRetention a α R * (∫ ξ, φ ξ ∂ccmPositiveFrequencyMeasure a α R) ≤
      ccmPositiveFrequencyGramCeiling a α R * ‖f‖ ^ 2 at hdebt
  have hl := ccmRestrictedWeilSource_ge_retainedPositiveWindow a α R
    ⟨ccmPositiveFrequencyRetention a α R, ccmPositiveFrequencyRetention_bounds a α R⟩ u.1
  change α * ‖f‖ ^ 2 - ((∫ ξ, φ ξ ∂ccmActualSourceNegativeMeasure a α) -
    ccmPositiveFrequencyRetention a α R * (∫ ξ, φ ξ ∂ccmPositiveFrequencyMeasure a α R)) ≤ _ at hl
  change (α - ccmPositiveFrequencyGramCeiling a α R) * ‖f‖ ^ 2 ≤ _
  nlinarith only [hl,hdebt]

theorem ccmRestrictedWeilPolarGround_ge_positiveFrequencyGram
    (a : SuzukiPositiveAperture) (α R : ℝ) :
    α - ccmPositiveFrequencyGramCeiling a α R ≤ ccmRestrictedWeilPolarGroundEnergy a := by
  apply le_ccmRestrictedWeilPolarGroundEnergy_of_floor
  intro u hu
  exact ccmRestrictedWeilSource_ge_positiveFrequencyGram a α R ⟨u,hu⟩

/-- The original determinant curvature and the retained positive-frequency saving add exactly. -/
theorem ccmPositiveFrequencyGramCeiling_sq_add_totalSaving
    (a : SuzukiPositiveAperture) (α R : ℝ) :
    ccmPositiveFrequencyGramCeiling a α R ^ 2 +
      (ccmActualSourceGramCurvature a α + ccmPositiveFrequencyGramSaving a α R) =
        ccmActualSourceNegativeTrace a α ^ 2 := by
  have h := ccmPositiveFrequencyGramCeiling_sq_add_saving a α R
  have hc := ccmActualSourceGramCeiling_sq_add_curvature a α
  linarith only [h,hc]

theorem ccmPositiveFrequencyGramCeiling_le_trace_sub_totalSaving
    (a : SuzukiPositiveAperture) (α R : ℝ) :
    ccmPositiveFrequencyGramCeiling a α R ≤ ccmActualSourceNegativeTrace a α -
      (ccmActualSourceGramCurvature a α + ccmPositiveFrequencyGramSaving a α R) /
        (2 * ccmActualSourceNegativeTrace a α) := by
  let T := ccmActualSourceNegativeTrace a α
  let C := ccmPositiveFrequencyGramCeiling a α R
  let D := ccmActualSourceGramCurvature a α + ccmPositiveFrequencyGramSaving a α R
  have hT : 0 ≤ T := integral_nonneg fun _ => sq_nonneg _
  have he : C ^ 2 + D = T ^ 2 := ccmPositiveFrequencyGramCeiling_sq_add_totalSaving a α R
  have hCT : C ≤ T := (ccmPositiveFrequencyGramCeiling_le_old a α R).trans
    (ccmPolarFourier_gram_le_trace a _)
  change C ≤ T - D / (2*T)
  by_cases hz : T = 0
  · simp only [hz, mul_zero, div_zero, sub_zero]
    simpa only [hz] using hCT
  · have hp : 0 < 2*T := by positivity
    have h : D/(2*T) ≤ T-C := by
      apply (div_le_iff₀ hp).mpr
      nlinarith [sq_nonneg (T-C)]
    linarith only [h]

/-- The full source receives both independently nonnegative savings, at every coefficient order. -/
theorem ccmRestrictedWeilSource_ge_totalGramSaving
    (a : SuzukiPositiveAperture) (α R : ℝ) (u : ccmPolarConstraintSubmodule a) :
    (α - ccmActualSourceNegativeTrace a α +
      (ccmActualSourceGramCurvature a α + ccmPositiveFrequencyGramSaving a α R) /
        (2 * ccmActualSourceNegativeTrace a α)) * ‖ccmArchimedeanFormToAperture a u.1‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u.1 := by
  have h := ccmPositiveFrequencyGramCeiling_le_trace_sub_totalSaving a α R
  have hm := mul_le_mul_of_nonneg_right h (sq_nonneg ‖ccmArchimedeanFormToAperture a u.1‖)
  have hl := ccmRestrictedWeilSource_ge_positiveFrequencyGram a α R u
  nlinarith only [hm,hl]

end RHTower
