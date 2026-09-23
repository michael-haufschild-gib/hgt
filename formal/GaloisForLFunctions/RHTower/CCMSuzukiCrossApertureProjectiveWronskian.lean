import GaloisForLFunctions.RHTower.CCMSuzukiCrossApertureRieszTransport
import GaloisForLFunctions.RHTower.CCMSuzukiV2ProjectiveRawCarrier
import GaloisForLFunctions.RHTower.SuzukiTaMovableCompletedCovarianceCharacteristic
import GaloisForLFunctions.RHTower.SuzukiTaMovableCompletedCovarianceSchur
import GaloisForLFunctions.RHTower.SuzukiTaV2ActualDefectJet
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
      (z ^ (2 : ℕ) + 1) * suzukiTaV2CrossApertureRawWronskian a b z := by
  rw [suzukiTaV2RawCharacteristicA_eq_rawCompletedFourier,
    suzukiTaV2RawCharacteristicE_eq_rawCompletedFourier,
    suzukiTaV2RawCharacteristicA_eq_rawCompletedFourier,
    suzukiTaV2RawCharacteristicE_eq_rawCompletedFourier]
  unfold suzukiTaV2CrossApertureRawWronskian
  have hI : (I : ℂ) ^ (2 : ℕ) = -1 := by norm_num
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
      ((z ^ (2 : ℕ) + 1) * suzukiTaV2CrossApertureRawWronskian a b z) /
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

/-- The raw upper coordinate is entire. -/
theorem differentiable_suzukiTaV2RawCharacteristicA
    (a : SuzukiPositiveAperture) :
    Differentiable ℂ (suzukiTaV2RawCharacteristicA a) := by
  unfold suzukiTaV2RawCharacteristicA
  exact (differentiable_id.sub_const I).mul
    (differentiable_suzukiTaPhysicalFourier a (suzukiTaRawDeficiency a 1))

/-- The raw lower coordinate is entire. -/
theorem differentiable_suzukiTaV2RawCharacteristicE
    (a : SuzukiPositiveAperture) :
    Differentiable ℂ (suzukiTaV2RawCharacteristicE a) := by
  unfold suzukiTaV2RawCharacteristicE
  exact (differentiable_id.add_const I).mul
    ((differentiable_suzukiTaPhysicalFourier a (suzukiTaRawDeficiency a (-1))).comp
      (by fun_prop))

/-- The raw completed plus-source Fourier coordinate is entire. -/
theorem differentiable_suzukiTaV2RawCompletedFourier
    (a : SuzukiPositiveAperture) :
    Differentiable ℂ (suzukiTaV2RawCompletedFourier a) := by
  unfold suzukiTaV2RawCompletedFourier
  exact differentiable_suzukiCompactL2Fourier a.2.le _

/-- The literal cross-aperture completed-source Wronskian is entire. -/
theorem differentiable_suzukiTaV2CrossApertureRawWronskian
    (a b : SuzukiPositiveAperture) :
    Differentiable ℂ (suzukiTaV2CrossApertureRawWronskian a b) := by
  unfold suzukiTaV2CrossApertureRawWronskian
  exact (differentiable_suzukiTaV2RawCompletedFourier b).mul
      ((differentiable_suzukiTaV2RawCompletedFourier a).comp (by fun_prop)) |>.sub
    ((differentiable_suzukiTaV2RawCompletedFourier a).mul
      ((differentiable_suzukiTaV2RawCompletedFourier b).comp (by fun_prop)))

theorem suzukiTaV2RawCharacteristicA_I
    (a : SuzukiPositiveAperture) : suzukiTaV2RawCharacteristicA a I = 0 := by
  simp [suzukiTaV2RawCharacteristicA]

/-- At the common anchor, differentiating the actual finite characteristic
recovers the raw upper coordinate after multiplication by its raw lower
coordinate. -/
theorem deriv_suzukiTaV2Livsic_mul_rawCharacteristicE
    (a : SuzukiPositiveAperture) :
    deriv (suzukiTaV2Livsic a) I * suzukiTaV2RawCharacteristicE a I =
      deriv (suzukiTaV2RawCharacteristicA a) I := by
  have hE : suzukiTaV2RawCharacteristicE a I ≠ 0 :=
    suzukiTaV2RawCharacteristicE_ne_zero_upperHalfPlane a (by norm_num)
  have hA := differentiable_suzukiTaV2RawCharacteristicA a
  have hEd := differentiable_suzukiTaV2RawCharacteristicE a
  have hquot : suzukiTaV2Livsic a =
      suzukiTaV2RawCharacteristicA a / suzukiTaV2RawCharacteristicE a := by
    funext z
    change suzukiTaV2Livsic a z =
      suzukiTaV2RawCharacteristicA a z / suzukiTaV2RawCharacteristicE a z
    exact suzukiTaV2Livsic_eq_rawDeficiency a z
  rw [hquot]
  have hdiv := (hA I).hasDerivAt.div (hEd I).hasDerivAt hE
  rw [hdiv.deriv]
  rw [suzukiTaV2RawCharacteristicA_I]
  field_simp [hE]
  ring

/-- The first source coefficient of the aperture Wronskian is exactly the
difference of the first finite projective jets. -/
theorem suzukiTaV2CrossApertureRawWronskian_anchor_deriv
    (a b : SuzukiPositiveAperture) :
    (2 * I) * suzukiTaV2CrossApertureRawWronskian a b I =
      (suzukiTaV2RawCharacteristicE b I * suzukiTaV2RawCharacteristicE a I) *
        (deriv (suzukiTaV2Livsic b) I - deriv (suzukiTaV2Livsic a) I) := by
  let A := fun c : SuzukiPositiveAperture => suzukiTaV2RawCharacteristicA c
  let E := fun c : SuzukiPositiveAperture => suzukiTaV2RawCharacteristicE c
  let W := suzukiTaV2CrossApertureRawWronskian a b
  have hA_a := differentiable_suzukiTaV2RawCharacteristicA a
  have hA_b := differentiable_suzukiTaV2RawCharacteristicA b
  have hE_a := differentiable_suzukiTaV2RawCharacteristicE a
  have hE_b := differentiable_suzukiTaV2RawCharacteristicE b
  have hW := differentiable_suzukiTaV2CrossApertureRawWronskian a b
  have hfac : HasDerivAt (fun z : ℂ => z ^ (2 : ℕ) + 1) (2 * I) I := by
    have hbase : HasDerivAt (fun z : ℂ => z * z + 1) (I + I) I := by
      simpa only [Pi.mul_apply, id_eq, one_mul, mul_one] using
        ((hasDerivAt_id I).mul (hasDerivAt_id I)).add_const 1
    simpa only [pow_two, two_mul] using hbase
  have hleft : HasDerivAt
      (fun z => A b z * E a z - A a z * E b z)
      (deriv (A b) I * E a I + A b I * deriv (E a) I -
        (deriv (A a) I * E b I + A a I * deriv (E b) I)) I := by
    exact ((hA_b I).hasDerivAt.mul (hE_a I).hasDerivAt).sub
      ((hA_a I).hasDerivAt.mul (hE_b I).hasDerivAt)
  have hright : HasDerivAt
      (fun z => (z ^ (2 : ℕ) + 1) * W z)
      ((2 * I) * W I + (I ^ (2 : ℕ) + 1) * deriv W I) I := by
    exact hfac.mul (hW I).hasDerivAt
  have hcross : (fun z => A b z * E a z - A a z * E b z) =
      fun z => (z ^ (2 : ℕ) + 1) * W z := by
    funext z
    exact suzukiTaV2RawCharacteristic_crossAperture_denominatorCleared a b z
  have hderiv :
      deriv (fun z => A b z * E a z - A a z * E b z) I =
        deriv (fun z => (z ^ (2 : ℕ) + 1) * W z) I := by rw [hcross]
  have hraw :
      deriv (A b) I * E a I + A b I * deriv (E a) I -
        (deriv (A a) I * E b I + A a I * deriv (E b) I) =
        (2 * I) * W I + (I ^ (2 : ℕ) + 1) * deriv W I := by
    rw [← hleft.deriv, hderiv, hright.deriv]
  have hAa : A a I = 0 := suzukiTaV2RawCharacteristicA_I a
  have hAb : A b I = 0 := suzukiTaV2RawCharacteristicA_I b
  have hderA_a := deriv_suzukiTaV2Livsic_mul_rawCharacteristicE a
  have hderA_b := deriv_suzukiTaV2Livsic_mul_rawCharacteristicE b
  dsimp only [A, E, W] at hraw hAa hAb hderA_a hderA_b ⊢
  rw [hAa, hAb] at hraw
  norm_num at hraw
  rw [← hderA_a, ← hderA_b] at hraw
  linear_combination -hraw

/-- **Exact first-mode source law.** The anchor value of the normalized
cross-aperture raw completed-source Wronskian is minus one quarter of the
literal completed even--odd covariance defect increment.  Thus existing
energy information controls this one mode only; no cofinal conclusion is
asserted for the remaining entire source current. -/
theorem suzukiTaV2CrossApertureRawWronskian_anchor_eq_defect_increment
    (a b : SuzukiPositiveAperture) :
    suzukiTaV2CrossApertureRawWronskian a b I /
        (suzukiTaV2RawCharacteristicE b I * suzukiTaV2RawCharacteristicE a I) =
      -((suzukiDefectAngle (suzukiTaCoalescingEvenEnergy b 1)
          (suzukiTaCoalescingOddEnergy b 1) : ℂ) -
        (suzukiDefectAngle (suzukiTaCoalescingEvenEnergy a 1)
          (suzukiTaCoalescingOddEnergy a 1) : ℂ)) / 4 := by
  have hEa : suzukiTaV2RawCharacteristicE a I ≠ 0 :=
    suzukiTaV2RawCharacteristicE_ne_zero_upperHalfPlane a (by norm_num)
  have hEb : suzukiTaV2RawCharacteristicE b I ≠ 0 :=
    suzukiTaV2RawCharacteristicE_ne_zero_upperHalfPlane b (by norm_num)
  have hW := suzukiTaV2CrossApertureRawWronskian_anchor_deriv a b
  rw [suzukiTaV2_coalescingDefectAngle_eq_two_I_mul_deriv,
    suzukiTaV2_coalescingDefectAngle_eq_two_I_mul_deriv]
  let E := suzukiTaV2RawCharacteristicE b I * suzukiTaV2RawCharacteristicE a I
  let D := deriv (suzukiTaV2Livsic b) I - deriv (suzukiTaV2Livsic a) I
  have htarget :
      -(2 * I * deriv (suzukiTaV2Livsic b) I -
          2 * I * deriv (suzukiTaV2Livsic a) I) / 4 =
        -(2 * I * D) / 4 := by
    dsimp only [D]
    ring
  rw [htarget]
  change suzukiTaV2CrossApertureRawWronskian a b I / E = -(2 * I * D) / 4
  change (2 * I) * suzukiTaV2CrossApertureRawWronskian a b I = E * D at hW
  have hE : E ≠ 0 := mul_ne_zero hEb hEa
  calc
    suzukiTaV2CrossApertureRawWronskian a b I / E =
        ((2 * I) * suzukiTaV2CrossApertureRawWronskian a b I) /
          ((2 * I) * E) := by
      field_simp [hE]
    _ = (E * D) / ((2 * I) * E) := by rw [hW]
    _ = D / (2 * I) := by
      field_simp [hE]
    _ = -(2 * I * D) / 4 := by
      have hI : (I : ℂ) ^ (2 : ℕ) = -1 := by norm_num
      field_simp
      ring_nf
      rw [hI]
      ring

end RHTower
