import GaloisForLFunctions.RHTower.CCMSuzukiCrossApertureRieszTransport
import GaloisForLFunctions.RHTower.CCMSuzukiV2ProjectiveRawCarrier
import GaloisForLFunctions.RHTower.SuzukiTaMovableCompletedCovarianceCharacteristic
import GaloisForLFunctions.RHTower.SuzukiTaMovableCompletedCovarianceSchur
import GaloisForLFunctions.RHTower.SoninCompressedWeylHolonomy
import GaloisForLFunctions.RHTower.HalfLineMultiplierChart

/-!
# Source-faithful projective aperture Wronskian

The literal Suzuki-v2 raw characteristic has a denominator-cleared aperture
increment.  This file identifies it with a completed-source Wronskian and
then decomposes that Wronskian into the physical shell and metric-response
terms.  It removes normalization drift from the convergence question without
asserting a cofinal bound for the remaining signed Wronskian.
-/

open Complex MeasureTheory Set

noncomputable section
namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

theorem suzukiCutoff_mono_of_fixed
    {a b : ℝ} (hab : a ≤ b) {p : SoninL2}
    (hp : suzukiCutoff a p = p) :
    suzukiCutoff b p = p := by
  change indicatorCutoff (Icc (-b) b) measurableSet_Icc p = p
  rw [← hp]
  change indicatorCutoff (Icc (-b) b) measurableSet_Icc
      (indicatorCutoff (Icc (-a) a) measurableSet_Icc p) =
    indicatorCutoff (Icc (-a) a) measurableSet_Icc p
  change ((indicatorCutoff (Icc (-b) b) measurableSet_Icc) *
      (indicatorCutoff (Icc (-a) a) measurableSet_Icc)) p = _
  rw [indicatorCutoff_mul_of_superset _ _ measurableSet_Icc measurableSet_Icc]
  intro x hx
  exact ⟨(neg_le_neg hab).trans hx.1, hx.2.trans hab⟩

theorem suzukiCompactL2Fourier_mono_of_fixed
    {a b : ℝ} (hab : a ≤ b) {p : SoninL2}
    (hp : suzukiCutoff a p = p) (z : ℂ) :
    suzukiCompactL2Fourier b p z = suzukiCompactL2Fourier a p z := by
  unfold suzukiCompactL2Fourier
  rw [show indicatorCutoff (Icc (-b) b) measurableSet_Icc p = p from
      suzukiCutoff_mono_of_fixed hab hp]
  rw [show indicatorCutoff (Icc (-a) a) measurableSet_Icc p = p from hp]

theorem suzukiTaMovableCompletedCovarianceFourier_read_larger
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (z : ℂ) :
    suzukiCompactL2Fourier b.1
      (suzukiTaMovableCompletedCovarianceSource a 1) z =
      suzukiTaMovableCompletedCovarianceFourier a 1 z := by
  have hfix : suzukiCutoff a.1
      (suzukiTaMovableCompletedCovarianceSource a 1) =
        suzukiTaMovableCompletedCovarianceSource a 1 := by
    exact soninCentralCutoff_suzukiTaMovableCompletedCovarianceSource a 1
  rw [suzukiCompactL2Fourier_mono_of_fixed hab hfix]
  change suzukiCompactL2Fourier a.1
      (suzukiTaMovableCompletedCovarianceSource a 1) z =
    suzukiCompactL2Fourier a.1
      (suzukiTaMovableCompletedCovarianceSource a 1) ((1 : ℂ) * z)
  rw [one_mul]

theorem suzukiTaV2RawCharacteristicA_eq_movableFourier
    (a : SuzukiPositiveAperture) (z : ℂ) :
    suzukiTaV2RawCharacteristicA a z =
      (z - I) * suzukiTaMovableCompletedCovarianceFourier a 1 z := by
  rw [suzukiTaV2RawCharacteristicA,
    suzukiTaMovableCompletedCovarianceFourier_eq_physical a 1]
  norm_num

theorem suzukiTaV2RawCharacteristicE_eq_movableFourier
    (a : SuzukiPositiveAperture) (z : ℂ) :
    suzukiTaV2RawCharacteristicE a z =
      (z + I) * suzukiTaMovableCompletedCovarianceFourier a 1 (-z) := by
  rw [suzukiTaV2RawCharacteristicE,
    suzukiTaPhysicalFourier_rawDeficiency_reflection a 1 z,
    suzukiTaMovableCompletedCovarianceFourier_eq_physical a 1]
  norm_num

theorem suzukiCompactL2Fourier_add
    {a : ℝ} (ha : 0 ≤ a) (f g : SoninL2) (z : ℂ) :
    suzukiCompactL2Fourier a (f + g) z =
      suzukiCompactL2Fourier a f z + suzukiCompactL2Fourier a g z := by
  unfold suzukiCompactL2Fourier
  rw [map_add]
  rw [← integral_add
    (integrable_suzukiCompactL2Fourier_integrand ha f z)
    (integrable_suzukiCompactL2Fourier_integrand ha g z)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add
    (indicatorCutoff (Icc (-a) a) measurableSet_Icc f)
    (indicatorCutoff (Icc (-a) a) measurableSet_Icc g)] with x hx
  rw [hx]
  simp only [Pi.add_apply, suzukiCutoff]
  ring

/-- Unscaled literal Fourier coordinate of actual plus covariance source. -/
def suzukiTaV2RawCompletedFourier
    (a : SuzukiPositiveAperture) (z : ℂ) : ℂ :=
  suzukiCompactL2Fourier a.1
    (suzukiTaMovableCompletedCovarianceSource a 1) z

theorem suzukiTaV2RawCompletedFourier_eq_movable
    (a : SuzukiPositiveAperture) (z : ℂ) :
    suzukiTaV2RawCompletedFourier a z =
      suzukiTaMovableCompletedCovarianceFourier a 1 z := by
  change suzukiCompactL2Fourier a.1
      (suzukiTaMovableCompletedCovarianceSource a 1) z =
    suzukiCompactL2Fourier a.1
      (suzukiTaMovableCompletedCovarianceSource a 1) ((1 : ℂ) * z)
  rw [one_mul]

theorem suzukiTaV2RawCompletedFourier_read_larger
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (z : ℂ) :
    suzukiCompactL2Fourier b.1
      (suzukiTaMovableCompletedCovarianceSource a 1) z =
      suzukiTaV2RawCompletedFourier a z := by
  exact suzukiCompactL2Fourier_mono_of_fixed hab
    (soninCentralCutoff_suzukiTaMovableCompletedCovarianceSource a 1) z

def suzukiTaRieszMetricShiftGap
    {a b : SuzukiPositiveAperture} (_hab : a.1 ≤ b.1) : ℂ :=
  ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) -
    boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b) : ℝ) : ℂ)

def suzukiTaRieszMetricResponseSource
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (eps : ℝ) : SoninL2 :=
  suzukiApertureZeroExtendL2
    (suzukiWeilIntervalCovariance b
      (suzukiWeilIntervalFormEmbedding b
        (ccmArchimedeanFormDomain_extension hab
          (suzukiTaToFormCLM a (suzukiTaRawDeficiency a eps)))))

def suzukiTaRieszMetricShellSource
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (eps : ℝ) : SoninL2 :=
  suzukiApertureZeroExtendL2
    (suzukiWeilIntervalFormEmbedding b
      (suzukiTaRiesz_metricRenormalizedShell hab eps))

theorem suzukiTaRieszMetricShellSource_eq
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (eps : ℝ) :
    suzukiTaRieszMetricShellSource hab eps =
      suzukiTaMovableCompletedCovarianceSource b eps -
        suzukiTaMovableCompletedCovarianceSource a eps -
          suzukiTaRieszMetricShiftGap hab •
            suzukiTaRieszMetricResponseSource hab eps := by
  simpa only [suzukiTaRieszMetricShellSource,
    suzukiTaRieszMetricShiftGap, suzukiTaRieszMetricResponseSource] using
    suzukiTaRiesz_metricRenormalizedShell_physical_eq hab eps

theorem suzukiTaMovableCompletedCovarianceSource_crossAperture_increment
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (eps : ℝ) :
    suzukiTaMovableCompletedCovarianceSource b eps =
      suzukiTaMovableCompletedCovarianceSource a eps +
        suzukiTaRieszMetricShellSource hab eps +
          suzukiTaRieszMetricShiftGap hab •
            suzukiTaRieszMetricResponseSource hab eps := by
  rw [suzukiTaRieszMetricShellSource_eq]
  module

def suzukiTaRieszMetricShellFourier
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (z : ℂ) : ℂ :=
  suzukiCompactL2Fourier b.1 (suzukiTaRieszMetricShellSource hab 1) z

def suzukiTaRieszMetricResponseFourier
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (z : ℂ) : ℂ :=
  suzukiCompactL2Fourier b.1 (suzukiTaRieszMetricResponseSource hab 1) z

theorem suzukiTaV2RawCompletedFourier_crossAperture_increment
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (z : ℂ) :
    suzukiTaV2RawCompletedFourier b z =
      suzukiTaV2RawCompletedFourier a z +
        suzukiTaRieszMetricShellFourier hab z +
          suzukiTaRieszMetricShiftGap hab *
            suzukiTaRieszMetricResponseFourier hab z := by
  unfold suzukiTaV2RawCompletedFourier
  rw [suzukiTaMovableCompletedCovarianceSource_crossAperture_increment hab 1,
    suzukiCompactL2Fourier_add b.2.le,
    suzukiCompactL2Fourier_add b.2.le,
    suzukiCompactL2Fourier_smul,
    suzukiTaV2RawCompletedFourier_read_larger hab]
  rfl

def suzukiTaV2CrossApertureRawWronskian
    (a b : SuzukiPositiveAperture) (z : ℂ) : ℂ :=
  suzukiTaV2RawCompletedFourier b z *
      suzukiTaV2RawCompletedFourier a (-z) -
    suzukiTaV2RawCompletedFourier a z *
      suzukiTaV2RawCompletedFourier b (-z)

theorem suzukiTaV2CrossApertureRawWronskian_eq_shell_metric
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (z : ℂ) :
    suzukiTaV2CrossApertureRawWronskian a b z =
      suzukiTaRieszMetricShellFourier hab z *
          suzukiTaV2RawCompletedFourier a (-z) -
        suzukiTaV2RawCompletedFourier a z *
          suzukiTaRieszMetricShellFourier hab (-z) +
        suzukiTaRieszMetricShiftGap hab *
          (suzukiTaRieszMetricResponseFourier hab z *
              suzukiTaV2RawCompletedFourier a (-z) -
            suzukiTaV2RawCompletedFourier a z *
              suzukiTaRieszMetricResponseFourier hab (-z)) := by
  unfold suzukiTaV2CrossApertureRawWronskian
  rw [suzukiTaV2RawCompletedFourier_crossAperture_increment hab,
    suzukiTaV2RawCompletedFourier_crossAperture_increment hab]
  ring

theorem suzukiTaV2RawCharacteristicA_eq_rawCompletedFourier
    (a : SuzukiPositiveAperture) (z : ℂ) :
    suzukiTaV2RawCharacteristicA a z =
      (z - I) * suzukiTaV2RawCompletedFourier a z := by
  rw [suzukiTaV2RawCharacteristicA_eq_movableFourier,
    ← suzukiTaV2RawCompletedFourier_eq_movable]

theorem suzukiTaV2RawCharacteristicE_eq_rawCompletedFourier
    (a : SuzukiPositiveAperture) (z : ℂ) :
    suzukiTaV2RawCharacteristicE a z =
      (z + I) * suzukiTaV2RawCompletedFourier a (-z) := by
  rw [suzukiTaV2RawCharacteristicE_eq_movableFourier,
    ← suzukiTaV2RawCompletedFourier_eq_movable]

theorem suzukiTaV2RawCharacteristic_crossAperture_denominatorCleared
    (a b : SuzukiPositiveAperture) (z : ℂ) :
    suzukiTaV2RawCharacteristicA b z * suzukiTaV2RawCharacteristicE a z -
      suzukiTaV2RawCharacteristicA a z * suzukiTaV2RawCharacteristicE b z =
      (z ^ 2 + 1) * suzukiTaV2CrossApertureRawWronskian a b z := by
  rw [suzukiTaV2RawCharacteristicA_eq_rawCompletedFourier,
    suzukiTaV2RawCharacteristicE_eq_rawCompletedFourier,
    suzukiTaV2RawCharacteristicA_eq_rawCompletedFourier,
    suzukiTaV2RawCharacteristicE_eq_rawCompletedFourier]
  unfold suzukiTaV2CrossApertureRawWronskian
  have hI : (I : ℂ) ^ 2 = -1 := by norm_num
  ring_nf
  rw [hI]
  ring

/-- The raw lower characteristic coordinate has no upper-half-plane zero.
This transfers finite self-adjoint spectral reality through the common raw
normalization, rather than assuming a source denominator bound. -/
theorem suzukiTaV2RawCharacteristicE_ne_zero_upperHalfPlane
    (a : SuzukiPositiveAperture) {z : ℂ} (hz : 0 < z.im) :
    suzukiTaV2RawCharacteristicE a z ≠ 0 := by
  have hnormal : suzukiTaV2CharacteristicE a z ≠ 0 :=
    suzukiLivsic_denominator_ne_zero
      (differentiable_suzukiTaV2CharacteristicA a).continuous
      (differentiable_suzukiTaV2CharacteristicE a).continuous
      (suzukiTaV2CharacteristicA_I a) (suzukiTaV2_allAngleRealZeros a) hz
  intro hraw
  apply hnormal
  rw [suzukiTaV2CharacteristicE_eq_commonScale_raw]
  simp [hraw]

/-- Exact upper-half-plane projective transport law.  The literal difference
of finite Suzuki characteristics is the multiplier-weighted raw completed
source Wronskian divided by its two actual nonzero denominator coordinates. -/
theorem suzukiTaV2Livsic_sub_eq_rawWronskian_div
    (a b : SuzukiPositiveAperture) {z : ℂ} (hz : 0 < z.im) :
    suzukiTaV2Livsic b z - suzukiTaV2Livsic a z =
      ((z ^ 2 + 1) * suzukiTaV2CrossApertureRawWronskian a b z) /
        (suzukiTaV2RawCharacteristicE b z * suzukiTaV2RawCharacteristicE a z) := by
  have hEa : suzukiTaV2RawCharacteristicE a z ≠ 0 :=
    suzukiTaV2RawCharacteristicE_ne_zero_upperHalfPlane a hz
  have hEb : suzukiTaV2RawCharacteristicE b z ≠ 0 :=
    suzukiTaV2RawCharacteristicE_ne_zero_upperHalfPlane b hz
  rw [suzukiTaV2Livsic_eq_rawDeficiency,
    suzukiTaV2Livsic_eq_rawDeficiency]
  simp only [suzukiLivsicQuotient]
  field_simp [hEa, hEb]
  simpa [mul_comm] using
    suzukiTaV2RawCharacteristic_crossAperture_denominatorCleared a b z

end RHTower
