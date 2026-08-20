import GaloisForLFunctions.RHTower.DeningerTraceBound
import GaloisForLFunctions.RHTower.HedenmalmThetaAnomalyBurnolGaussianRelativeSplitting
import GaloisForLFunctions.RHTower.HedenmalmThetaCompactFluxEnergy
import GaloisForLFunctions.RHTower.HedenmalmWardGreenRemovableExtensionKernelProjection
import GaloisForLFunctions.RHTower.HeatTraceSensitivity
import GaloisForLFunctions.RHTower.PrimeArchThetaMorseAnomalousDarboux
import GaloisForLFunctions.RHTower.RouteEFinitePhysicalCodiagonalGaugeCollapse
import GaloisForLFunctions.RHTower.SigmaOrbit
import GaloisForLFunctions.RHTower.SuzukiAffineResolventKreinDefect
import GaloisForLFunctions.RHTower.SuzukiMarkedSecantMidpointLorentzCompletion
import GaloisForLFunctions.RHTower.ThetaWignerEisensteinCrossEnergy
import GaloisForLFunctions.RHTower.XiEndpointReflectionDefectEnergy
import GaloisForLFunctions.RHTower.XiGlobalReflectionDefectEnergy
import GaloisForLFunctions.RHTower.XiHeatCassiniPhaseClockLanding
import GaloisForLFunctions.RHTower.XiHorizontalCollisionWardGreenCayleyQuantum
import GaloisForLFunctions.RHTower.XiRadialJensenSchurCapacity
import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniResolventSourceLaw
import GaloisForLFunctions.RHTower.XiSquaredSeamPowerSixtyFourMassCriterion
import GaloisForLFunctions.RHTower.XiThermalQuadraticReflectionDefectSpectrum
import GaloisForLFunctions.RHTower.XiWardEdgeEnergyPhaseQuantizationUniversalityLaw

/-!
# Bogomolny--Prasad--Sommerfield bounds in RHTower

Unconditional energy--charge decompositions, lower bounds, and saturation laws mechanically
extracted from existing RHTower objects.
-/

open MeasureTheory Set
open scoped BigOperators

namespace RHTower

open HedenmalmThetaSource

noncomputable section

/-! ## Deninger radial modes -/

/-- Unit-frequency Poisson mode energy. -/
def deningerUnitModeBPSEnergy : ℝ :=
  ∫ r in Ioi (0 : ℝ), ((-|(1 : ℝ)| * deningerModeProfile 1 r) ^ 2 +
    (1 : ℝ) ^ 2 * deningerModeProfile 1 r ^ 2)

/-- Unit-frequency Poisson mode saturates the boundary charge. -/
theorem deningerUnitModeBPSEnergy_eq_charge : deningerUnitModeBPSEnergy = 1 := by
  rw [deningerUnitModeBPSEnergy, deningerDirichlet_principle (by norm_num : (1 : ℝ) ≠ 0)]
  simp [deningerModeProfile]

/-- Negative-unit-frequency Poisson mode energy. -/
def deningerNegativeUnitModeBPSEnergy : ℝ :=
  ∫ r in Ioi (0 : ℝ), ((-|-1| * deningerModeProfile (-1) r) ^ 2 +
    (-1 : ℝ) ^ 2 * deningerModeProfile (-1) r ^ 2)

/-- Opposite chirality has the same saturated unit charge. -/
theorem deningerNegativeUnitModeBPSEnergy_eq_charge :
    deningerNegativeUnitModeBPSEnergy = 1 := by
  rw [deningerNegativeUnitModeBPSEnergy,
    deningerDirichlet_principle (by norm_num : (-1 : ℝ) ≠ 0)]
  simp [deningerModeProfile]

/-! ## Theta-cusp Morse state -/

/-- Constant Morse-dressed theta state obeys the first-order BPS equation. -/
theorem thetaCuspMorseConstant_bpsEquation (A : ℝ) (n : ℕ) (x : ℝ) :
    deriv (thetaCuspMorseDressedPolynomial A n 1) x +
        thetaCuspMorseSuperpotential A n x *
          thetaCuspMorseDressedPolynomial A n 1 x = 0 := by
  rw [thetaCuspMorse_supercharge_dressedPolynomial]
  simp

/-- Constant Morse-dressed theta BPS state has zero lower Hamiltonian energy. -/
theorem thetaCuspMorseConstant_bpsEnergy_zero (A : ℝ) (n : ℕ) (x : ℝ) :
    thetaCuspMorseHamiltonianMinus A n
      (thetaCuspMorseDressedPolynomial A n 1) x = 0 := by
  rw [thetaCuspMorseHamiltonianMinus_dressedPolynomial]
  simp

/-! ## Ward--Green--Cayley reflection charge -/

/-- Ward--Green--Cayley BPS defect above quantized reflection charge. -/
def xiWardGreenCayleyBPSDefect (T : ℝ) : ℝ :=
  xiStripWindowWardGreenCayleyReflectionEnergy T -
    16 * (xiReflectionSelfIntersectionCharge T : ℝ)

/-- Every finite Xi window obeys the quantized Ward--Green--Cayley BPS bound. -/
theorem xiWardGreenCayley_bpsBound (T : ℝ) :
    16 * (xiReflectionSelfIntersectionCharge T : ℝ) ≤
      xiStripWindowWardGreenCayleyReflectionEnergy T :=
  sixteen_mul_reflectionCharge_le_wardGreenCayleyEnergy T

/-- Corresponding Ward--Green--Cayley BPS defect is nonnegative. -/
theorem xiWardGreenCayleyBPSDefect_nonneg (T : ℝ) :
    0 ≤ xiWardGreenCayleyBPSDefect T := by
  exact sub_nonneg.mpr (xiWardGreenCayley_bpsBound T)

/-! ## Thermal and theta vacuum bounds -/

theorem xiThermalOrientationEnergy_bpsBound :
    0 ≤ xiThermalOrientationEnergy := xiThermalOrientationEnergy_nonneg

theorem xiThermalOrientationEnergy_bpsSaturation_iff :
    xiThermalOrientationEnergy = 0 ↔ RiemannHypothesis :=
  xiThermalOrientationEnergy_eq_zero_iff_rh

theorem xiThermalSquareReflectionDefectEnergy_bpsBound :
    0 ≤ xiThermalSquareReflectionDefectEnergy := by
  rw [xiThermalSquareReflectionDefectEnergy_eq_four_mul_orientationEnergy]
  exact mul_nonneg (by norm_num) xiThermalOrientationEnergy_nonneg

theorem xiThermalSquareReflectionDefectEnergy_bpsSaturation_iff :
    xiThermalSquareReflectionDefectEnergy = 0 ↔ RiemannHypothesis :=
  xiThermalSquareReflectionDefectEnergy_eq_zero_iff_rh

theorem thetaXiNormalizedRootFluxEnergy_bpsBound :
    0 ≤ thetaXiNormalizedRootFluxEnergy := thetaXiNormalizedRootFluxEnergy_nonneg

theorem thetaXiNormalizedRootFluxEnergy_bpsSaturation_iff :
    thetaXiNormalizedRootFluxEnergy = 0 ↔ RiemannHypothesis :=
  thetaXiNormalizedRootFluxEnergy_eq_zero_iff_riemannHypothesis

theorem thetaXiNormalizedRankTwoBoundaryFluxEnergy_bpsBound :
    0 ≤ thetaXiNormalizedRankTwoBoundaryFluxEnergy :=
  thetaXiNormalizedRankTwoBoundaryFluxEnergy_nonneg

theorem thetaXiNormalizedRankTwoBoundaryFluxEnergy_bpsSaturation_iff :
    thetaXiNormalizedRankTwoBoundaryFluxEnergy = 0 ↔ RiemannHypothesis :=
  thetaXiNormalizedRankTwoBoundaryFluxEnergy_eq_zero_iff_riemannHypothesis

/-! ## Global and endpoint reflection vacuum bounds -/

theorem xiGlobalReflectionDefectEnergy_bpsBound :
    0 ≤ xiGlobalReflectionDefectEnergy := xiGlobalReflectionDefectEnergy_nonneg

theorem xiGlobalReflectionDefectEnergy_bpsSaturation_iff :
    xiGlobalReflectionDefectEnergy = 0 ↔ RiemannHypothesis :=
  xiGlobalReflectionDefectEnergy_eq_zero_iff_rh

theorem xiEndpointReflectionDefectEnergy_bpsBound :
    0 ≤ xiEndpointReflectionDefectEnergy := xiEndpointReflectionDefectEnergy_nonneg

theorem xiEndpointReflectionDefectEnergy_bpsSaturation_iff :
    xiEndpointReflectionDefectEnergy = 0 ↔ RiemannHypothesis :=
  xiEndpointReflectionDefectEnergy_eq_zero_iff_rh

/-- Global source curvature is bounded by Hermitian mass through the reflection BPS defect. -/
theorem primeArchCentralCurvature_bpsBound :
    primeArchCentralCurvature ≤ xiReciprocalHermitianMass :=
  primeArchCentralCurvature_le_xiReciprocalHermitianMass

/-- Endpoint source curvature is bounded by raw Hermitian mass through the endpoint BPS defect. -/
theorem xiEndpointCompletedCurvature_bpsBound :
    xiEndpointCompletedCurvature ≤ xiRawReciprocalHermitianMass :=
  xiEndpointCompletedCurvature_le_rawMass

/-! ## Heat-Cassini unit-shift vacuum bound -/

theorem xiHeatCassiniUnitPhaseClockEnergy_bpsBound :
    0 ≤ xiHeatCassiniPhaseClockEnergy 1 := by
  rw [xiHeatCassiniPhaseClockEnergy_eq_orientationDefect one_pos]
  exact xiHeatCassiniOrientationDefect_nonneg one_pos

theorem xiHeatCassiniUnitPhaseClockEnergy_bpsSaturation_iff :
    xiHeatCassiniPhaseClockEnergy 1 = 0 ↔ RiemannHypothesis := by
  exact (riemannHypothesis_iff_xiHeatCassiniPhaseClockEnergy_eq_zero one_pos).symm

/-! ## Ward-edge phase energy -/

theorem xiWardEdgeQuadEnergy_bpsBound :
    (0 : ENNReal) ≤ xiWardEdgeQuadEnergy := bot_le

theorem xiWardEdgeQuadEnergy_bpsSaturation_iff :
    xiWardEdgeQuadEnergy = 0 ↔ RiemannHypothesis :=
  riemannHypothesis_iff_xiWardEdgeQuadEnergy_eq_zero.symm

/-! ## Cassini power charges -/

theorem xiSquaredSeamPowerThirtyTwoTransverseCharge_bpsBound :
    0 ≤ xiSquaredSeamPowerThirtyTwoTransverseCharge := by
  exact tsum_nonneg fun _ => sq_nonneg _

theorem xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy_bpsBound :
    4 * xiSquaredSeamPowerThirtyTwoTransverseCharge ≤
      xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy := by
  rw [xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy_eq_four_mul_transverseCharge]

theorem xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy_bpsSaturation_iff :
    xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy = 0 ↔ RiemannHypothesis :=
  xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy_eq_zero_iff_riemannHypothesis

theorem intrinsicCassiniJetResidual_bpsBound :
    0 ≤ 4096 * xiSquaredSeamCassiniPowerSixtyFourJensenIntegral.toReal +
      (iteratedDeriv 63 (logDeriv xiSquaredSeamCassiniSource) 0).re /
        ((63 : ℕ).factorial : ℝ) := intrinsicCassiniJetResidual_nonneg

theorem intrinsicCassiniJetResidual_bpsSaturation_iff :
    4096 * xiSquaredSeamCassiniPowerSixtyFourJensenIntegral.toReal +
        (iteratedDeriv 63 (logDeriv xiSquaredSeamCassiniSource) 0).re /
          ((63 : ℕ).factorial : ℝ) = 0 ↔ RiemannHypothesis :=
  intrinsicCassiniJetResidual_eq_zero_iff_riemannHypothesis

theorem xiSquaredSeamPowerSixtyFourDefectEnergy_bpsBound :
    2 * xiSquaredSeamPowerThirtyTwoTransverseCharge ≤
      xiSquaredSeamPowerSixtyFourDefectEnergy := by
  rw [xiSquaredSeamPowerSixtyFourDefectEnergy_eq_two_mul_transverseCharge]

theorem xiSquaredSeamPowerSixtyFourDefectEnergy_bpsSaturation_iff :
    xiSquaredSeamPowerSixtyFourDefectEnergy = 0 ↔ RiemannHypothesis := by
  rw [xiSquaredSeamPowerSixtyFourDefectEnergy_eq_two_mul_transverseCharge]
  constructor
  · intro h
    apply xiSquaredSeamPowerThirtyTwoTransverseCharge_eq_zero_iff_riemannHypothesis.mp
    nlinarith [xiSquaredSeamPowerThirtyTwoTransverseCharge_bpsBound]
  · intro hRH
    rw [xiSquaredSeamPowerThirtyTwoTransverseCharge_eq_zero_iff_riemannHypothesis.mpr hRH]
    norm_num

/-! ## Wigner--Eisenstein dual-channel bound -/

/-- Primal plus reciprocal-symbol energy of a Wigner cross channel. -/
def thetaWignerEisensteinBPSEnergy (b τ : ℝ) (z w : ℂ) : ℝ :=
  (thetaWignerEisensteinSymbol b τ * Complex.normSq z +
    Complex.normSq w / thetaWignerEisensteinSymbol b τ) / 2

/-- Signed Wigner cross charge. -/
def thetaWignerEisensteinBPSCharge (z w : ℂ) : ℝ :=
  -((starRingEnd ℂ) z * w).re

/-- Completed-square defect in the Wigner dual channel. -/
def thetaWignerEisensteinBPSDefect (b τ : ℝ) (z w : ℂ) : ℝ :=
  Complex.normSq (((thetaWignerEisensteinSymbol b τ : ℝ) : ℂ) * z + w) /
    (2 * thetaWignerEisensteinSymbol b τ)

/-- Exact Wigner--Eisenstein BPS decomposition. -/
theorem thetaWignerEisensteinBPSEnergy_eq_charge_add_defect
    (b τ : ℝ) (z w : ℂ) :
    thetaWignerEisensteinBPSEnergy b τ z w =
      thetaWignerEisensteinBPSCharge z w +
        thetaWignerEisensteinBPSDefect b τ z w := by
  have h := complexCrossEnergy_completeSquare
    (thetaWignerEisensteinSymbol_pos b τ) z w
  have hp := (thetaWignerEisensteinSymbol_pos b τ).ne'
  simp only [thetaWignerEisensteinBPSEnergy, thetaWignerEisensteinBPSCharge,
    thetaWignerEisensteinBPSDefect]
  field_simp [hp] at h ⊢
  linarith

/-- Wigner--Eisenstein BPS defect is nonnegative. -/
theorem thetaWignerEisensteinBPSDefect_nonneg
    (b τ : ℝ) (z w : ℂ) :
    0 ≤ thetaWignerEisensteinBPSDefect b τ z w := by
  exact div_nonneg (Complex.normSq_nonneg _)
    (mul_nonneg (by norm_num) (thetaWignerEisensteinSymbol_pos b τ).le)

/-- Wigner cross charge is bounded by primal plus reciprocal-symbol energy. -/
theorem thetaWignerEisensteinBPSCharge_le_energy
    (b τ : ℝ) (z w : ℂ) :
    thetaWignerEisensteinBPSCharge z w ≤
      thetaWignerEisensteinBPSEnergy b τ z w := by
  rw [thetaWignerEisensteinBPSEnergy_eq_charge_add_defect]
  exact le_add_of_nonneg_right (thetaWignerEisensteinBPSDefect_nonneg b τ z w)

/-- Wigner BPS saturation is cancellation of primal and dual amplitudes. -/
theorem thetaWignerEisensteinBPSSaturation_iff
    (b τ : ℝ) (z w : ℂ) :
    thetaWignerEisensteinBPSEnergy b τ z w =
        thetaWignerEisensteinBPSCharge z w ↔
      ((thetaWignerEisensteinSymbol b τ : ℝ) : ℂ) * z + w = 0 := by
  rw [thetaWignerEisensteinBPSEnergy_eq_charge_add_defect]
  have hp : 2 * thetaWignerEisensteinSymbol b τ ≠ 0 := by
    exact mul_ne_zero (by norm_num) (thetaWignerEisensteinSymbol_pos b τ).ne'
  constructor
  · intro h
    have hdefect : thetaWignerEisensteinBPSDefect b τ z w = 0 := by linarith
    unfold thetaWignerEisensteinBPSDefect at hdefect
    have hnorm : Complex.normSq
        (((thetaWignerEisensteinSymbol b τ : ℝ) : ℂ) * z + w) = 0 := by
      exact (div_eq_zero_iff).mp hdefect |>.resolve_right hp
    exact Complex.normSq_eq_zero.mp hnorm
  · intro h
    rw [thetaWignerEisensteinBPSDefect, h, Complex.normSq_zero, zero_div, add_zero]

/-! ## Suzuki midpoint Lorentz completion -/

/-- Minimal rooted completion energy of the marked Suzuki secant. -/
def suzukiMarkedSecantBPSEnergy (m d r s : ℝ) : ℝ :=
  suzukiMarkedSecantSymmetricForm m d r s r s + d ^ 2 * s ^ 2

/-- Minimal marked-secant completion is exactly one square. -/
theorem suzukiMarkedSecantBPSEnergy_eq_square (m d r s : ℝ) :
    suzukiMarkedSecantBPSEnergy m d r s = (r - m * s) ^ 2 :=
  suzukiMarkedSecant_minimalRootedCompletion_eq_square m d r s

/-- Minimal marked-secant BPS energy is nonnegative. -/
theorem suzukiMarkedSecantBPSEnergy_nonneg (m d r s : ℝ) :
    0 ≤ suzukiMarkedSecantBPSEnergy m d r s := by
  rw [suzukiMarkedSecantBPSEnergy_eq_square]
  exact sq_nonneg _

/-- Marked-secant BPS saturation is the midpoint first-order equation. -/
theorem suzukiMarkedSecantBPSSaturation_iff (m d r s : ℝ) :
    suzukiMarkedSecantBPSEnergy m d r s = 0 ↔ r = m * s := by
  rw [suzukiMarkedSecantBPSEnergy_eq_square, sq_eq_zero_iff, sub_eq_zero]

/-! ## Suzuki two-channel Krein completion -/

/-- Minimal unit-positive-block Schur completion energy. -/
def suzukiKreinMinimalBPSEnergy (coupling debt x y : ℝ) : ℝ :=
  suzukiTwoChannelKreinCompletionForm
    1 coupling (debt + coupling ^ 2) debt x y

/-- Minimal two-channel Krein completion is exactly one square. -/
theorem suzukiKreinMinimalBPSEnergy_eq_square (coupling debt x y : ℝ) :
    suzukiKreinMinimalBPSEnergy coupling debt x y =
      (x + coupling * y) ^ 2 := by
  rw [suzukiKreinMinimalBPSEnergy,
    suzukiTwoChannelKreinCompletionForm_eq_completedSquare
      (by norm_num : (1 : ℝ) ≠ 0)]
  norm_num

/-- Minimal two-channel Krein BPS energy is nonnegative. -/
theorem suzukiKreinMinimalBPSEnergy_nonneg (coupling debt x y : ℝ) :
    0 ≤ suzukiKreinMinimalBPSEnergy coupling debt x y := by
  rw [suzukiKreinMinimalBPSEnergy_eq_square]
  exact sq_nonneg _

/-- Krein BPS saturation cancels local and projective amplitudes. -/
theorem suzukiKreinMinimalBPSSaturation_iff (coupling debt x y : ℝ) :
    suzukiKreinMinimalBPSEnergy coupling debt x y = 0 ↔
      x = -coupling * y := by
  rw [suzukiKreinMinimalBPSEnergy_eq_square, sq_eq_zero_iff]
  constructor <;> intro h <;> linarith

/-! ## Burnol Gaussian reflection frame -/

/-- Burnol Gaussian reflection channel has zero topological charge. -/
def thetaXiBurnolGaussianBPSCharge (_q : XiZeroCopy) : ℝ :=
  0

/-- Burnol Gaussian reflection energy is nonnegative. -/
theorem thetaXiBurnolGaussianReflectionDefectEnergy_nonneg (q : XiZeroCopy) :
    0 ≤ thetaXiBurnolGaussianReflectionDefectEnergy q := by
  rw [thetaXiBurnolGaussianReflectionDefectEnergy_exact]
  exact mul_nonneg
    (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
    (burnolTwoPrimeFrameEnergy_pos (xiSpectralPoint q)).le

/-- Burnol Gaussian reflection energy obeys its zero-charge BPS bound. -/
theorem thetaXiBurnolGaussianBPSCharge_le_energy (q : XiZeroCopy) :
    thetaXiBurnolGaussianBPSCharge q ≤ thetaXiBurnolGaussianReflectionDefectEnergy q := by
  simpa [thetaXiBurnolGaussianBPSCharge] using
    thetaXiBurnolGaussianReflectionDefectEnergy_nonneg q

/-- Burnol Gaussian BPS saturation places the selected Xi zero on the critical line. -/
theorem thetaXiBurnolGaussianBPSSaturation_iff (q : XiZeroCopy) :
    thetaXiBurnolGaussianReflectionDefectEnergy q = thetaXiBurnolGaussianBPSCharge q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  simpa [thetaXiBurnolGaussianBPSCharge] using
    thetaXiBurnolGaussianReflectionDefectEnergy_eq_zero_iff q

/-! ## Ward--Green critical-line projection -/

/-- Full Ward--Green feature trace as BPS energy. -/
def wardGreenProjectionBPSEnergy (t : ℝ) : ℝ :=
  criticalFeatureHermitianEnergyTrace t

/-- Critical-line Ward--Green projection trace as BPS charge. -/
def wardGreenProjectionBPSCharge (t : ℝ) : ℝ :=
  criticalLineCriticalFeatureEnergyTrace t

/-- Off-line Ward--Green trace as BPS defect. -/
def wardGreenProjectionBPSDefect (t : ℝ) : ℝ :=
  offLineCriticalFeatureEnergyTrace t

/-- Exact Ward--Green projection BPS decomposition. -/
theorem wardGreenProjectionBPSEnergy_eq_charge_add_defect (t : ℝ) :
    wardGreenProjectionBPSEnergy t =
      wardGreenProjectionBPSCharge t + wardGreenProjectionBPSDefect t := by
  exact criticalFeatureHermitianEnergyTrace_eq_line_add_offLine t

/-- Off-line Ward--Green BPS defect is nonnegative. -/
theorem wardGreenProjectionBPSDefect_nonneg (t : ℝ) :
    0 ≤ wardGreenProjectionBPSDefect t := by
  unfold wardGreenProjectionBPSDefect offLineCriticalFeatureEnergyTrace
  exact tsum_nonneg (offLineCriticalFeatureEnergy_nonneg t)

/-- Full Ward--Green feature energy dominates its critical-line charge. -/
theorem wardGreenProjectionBPSCharge_le_energy (t : ℝ) :
    wardGreenProjectionBPSCharge t ≤ wardGreenProjectionBPSEnergy t := by
  rw [wardGreenProjectionBPSEnergy_eq_charge_add_defect]
  exact le_add_of_nonneg_right (wardGreenProjectionBPSDefect_nonneg t)

/-- Ward--Green projection BPS saturation is equivalent to RH. -/
theorem wardGreenProjectionBPSSaturation_iff_rh (t : ℝ) :
    wardGreenProjectionBPSEnergy t = wardGreenProjectionBPSCharge t ↔
      RiemannHypothesis := by
  simpa [wardGreenProjectionBPSEnergy, wardGreenProjectionBPSCharge, eq_comm] using
    criticalLineCriticalFeatureEnergyTrace_eq_full_iff_rh t

/-! ## Gaussian heat-pole square completion -/

/-- Quadratic Gaussian pole energy at unit heat scale. -/
def gaussianPoleBPSEnergy (u : ℝ) : ℝ :=
  u ^ 2 / 4 + 1 / 4

/-- Linear Gaussian pole charge at unit heat scale. -/
def gaussianPoleBPSCharge (u : ℝ) : ℝ :=
  u / 2

/-- Off-shell Gaussian pole defect. -/
def gaussianPoleBPSDefect (u : ℝ) : ℝ :=
  (u - 1) ^ 2 / 4

/-- Gaussian completed square is an exact BPS decomposition. -/
theorem gaussianPoleBPSEnergy_eq_charge_add_defect (u : ℝ) :
    gaussianPoleBPSEnergy u = gaussianPoleBPSCharge u + gaussianPoleBPSDefect u := by
  have h := gaussian_complete_square u 1 (by norm_num : (1 : ℝ) ≠ 0)
  norm_num at h
  unfold gaussianPoleBPSEnergy gaussianPoleBPSCharge gaussianPoleBPSDefect
  linarith

/-- Gaussian pole energy dominates its linear charge. -/
theorem gaussianPoleBPSCharge_le_energy (u : ℝ) :
    gaussianPoleBPSCharge u ≤ gaussianPoleBPSEnergy u := by
  rw [gaussianPoleBPSEnergy_eq_charge_add_defect]
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (by norm_num))

/-- Gaussian pole BPS saturation fixes the pole parameter to the unit heat scale. -/
theorem gaussianPoleBPSSaturation_iff (u : ℝ) :
    gaussianPoleBPSEnergy u = gaussianPoleBPSCharge u ↔ u = 1 := by
  rw [gaussianPoleBPSEnergy_eq_charge_add_defect]
  unfold gaussianPoleBPSDefect
  constructor
  · intro h
    have hz : (u - 1) ^ 2 = 0 := by linarith
    have := sq_eq_zero_iff.mp hz
    linarith
  · intro h
    subst u
    norm_num

/-! ## Radial Jensen--Schur reflection gap -/

/-- Radial Jensen mass as BPS energy. -/
def xiRadialJensenBPSEnergy : ℝ :=
  xiReciprocalHermitianMass

/-- Central prime--Archimedean curvature as radial Jensen charge. -/
def xiRadialJensenBPSCharge : ℝ :=
  primeArchCentralCurvature

/-- Half the global reflection energy is the radial Jensen BPS defect. -/
def xiRadialJensenBPSDefect : ℝ :=
  xiGlobalReflectionDefectEnergy / 2

/-- Exact radial Jensen BPS decomposition. -/
theorem xiRadialJensenBPSEnergy_eq_charge_add_defect :
    xiRadialJensenBPSEnergy = xiRadialJensenBPSCharge + xiRadialJensenBPSDefect := by
  unfold xiRadialJensenBPSEnergy xiRadialJensenBPSCharge xiRadialJensenBPSDefect
  linarith [xiReciprocalHermitianMass_sub_curvature]

/-- Radial Jensen BPS defect is nonnegative. -/
theorem xiRadialJensenBPSDefect_nonneg :
    0 ≤ xiRadialJensenBPSDefect := by
  exact div_nonneg xiGlobalReflectionDefectEnergy_nonneg (by norm_num)

/-- Radial Jensen mass dominates central curvature. -/
theorem xiRadialJensenBPSCharge_le_energy :
    xiRadialJensenBPSCharge ≤ xiRadialJensenBPSEnergy := by
  rw [xiRadialJensenBPSEnergy_eq_charge_add_defect]
  exact le_add_of_nonneg_right xiRadialJensenBPSDefect_nonneg

/-- Radial Jensen BPS saturation is equivalent to RH. -/
theorem xiRadialJensenBPSSaturation_iff_rh :
    xiRadialJensenBPSEnergy = xiRadialJensenBPSCharge ↔ RiemannHypothesis := by
  simpa [xiRadialJensenBPSEnergy, xiRadialJensenBPSCharge] using
    xiReciprocalHermitianMass_eq_curvature_iff_rh

end

end RHTower

namespace RHTower.RouteEFiniteColumnData

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Scalar mass-mismatch charge in the finite Pearson column geometry. -/
noncomputable def massMismatchBPSCharge (d : RouteEFiniteColumnData ι) : ℝ :=
  (d.pushedTotal - d.targetTotal) ^ 2 / d.targetTotal

/-- Centered Pearson channel is a nonnegative BPS defect. -/
theorem centeredEnergy_bpsDefect_nonneg (d : RouteEFiniteColumnData ι) :
    0 ≤ d.centeredEnergy := by
  unfold centeredEnergy
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (d.targetMass_pos i).le (sq_nonneg _)

/-- Exact Pearson BPS decomposition into mass charge and centered defect. -/
theorem chiSquare_eq_massMismatchBPSCharge_add_defect
    (d : RouteEFiniteColumnData ι) :
    d.chiSquare = d.massMismatchBPSCharge + d.centeredEnergy := by
  rw [massMismatchBPSCharge, d.chiSquare_eq_centeredEnergy_add_massDefect]
  ring

/-- Pearson energy dominates scalar mass-mismatch charge. -/
theorem massMismatchBPSCharge_le_chiSquare (d : RouteEFiniteColumnData ι) :
    d.massMismatchBPSCharge ≤ d.chiSquare := by
  rw [d.chiSquare_eq_massMismatchBPSCharge_add_defect]
  exact le_add_of_nonneg_right d.centeredEnergy_bpsDefect_nonneg

/-- Pearson BPS saturation is exactly vanishing centered likelihood-ratio energy. -/
theorem chiSquare_eq_massMismatchBPSCharge_iff (d : RouteEFiniteColumnData ι) :
    d.chiSquare = d.massMismatchBPSCharge ↔ d.centeredEnergy = 0 := by
  rw [d.chiSquare_eq_massMismatchBPSCharge_add_defect]
  constructor <;> intro h <;> linarith

end RHTower.RouteEFiniteColumnData

namespace GaloisForLFunctions

/-- Functional-equation BPS fixed points are exactly critical-line points. -/
theorem sigmaConj_bpsSaturation_iff_critical (s : ℂ) :
    sigmaConj s = s ↔ s.re = 1 / 2 := sigmaConj_fixed_iff_critical s

end GaloisForLFunctions
