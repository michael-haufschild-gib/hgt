import GaloisForLFunctions.RHTower.Suzuki.SuzukiAperturePositionReflection
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaV2ActualSecondDefectJet

open Complex MeasureTheory Set

noncomputable section
namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

theorem deriv_suzukiCompactL2Fourier_zeroExtend_negI_eq_positionInner
    (a : SuzukiPositiveAperture) (g : SuzukiApertureIntervalL2 a.1) :
    deriv (suzukiCompactL2Fourier a.1 (suzukiApertureZeroExtendL2 g)) (-I) =
      I * inner ℂ
        (suzukiAperturePosition a (suzukiTaExponentialL2 a 1)) g := by
  rw [(hasDerivAt_suzukiCompactL2Fourier a.2.le
    (suzukiApertureZeroExtendL2 g) (-I)).deriv]
  rw [suzukiApertureZeroExtendL2_cutoff]
  have hzero := suzukiApertureZeroExtendL2_coeFn g
  calc
    (∫ x : ℝ, (suzukiApertureZeroExtendL2 g : ℝ → ℂ) x *
        (I * (x : ℂ)) * Complex.exp (I * (-I) * (x : ℂ))) =
      ∫ x : ℝ, suzukiApertureZeroExtend g x *
        ((I * (x : ℂ)) * Complex.exp (I * (-I) * (x : ℂ))) := by
          apply integral_congr_ae
          filter_upwards [hzero] with x hx
          rw [hx]
          ring
    _ = ∫ x : SuzukiApertureInterval a.1, (g : SuzukiApertureInterval a.1 → ℂ) x *
        ((I * (x.1 : ℂ)) * Complex.exp (I * (-I) * (x.1 : ℂ))) :=
      integral_suzukiApertureZeroExtend_mul a.1 g _
    _ = I * inner ℂ
        (suzukiAperturePosition a (suzukiTaExponentialL2 a 1)) g := by
      rw [MeasureTheory.L2.inner_def, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [suzukiAperturePosition_ae a (suzukiTaExponentialL2 a 1),
        ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
          (suzukiTaExponentialContinuous a 1)] with x hpos hexp
      rw [hpos]
      change (g : SuzukiApertureInterval a.1 → ℂ) x *
          ((I * (x.1 : ℂ)) * Complex.exp (I * (-I) * (x.1 : ℂ))) =
        I * inner ℂ
          ((x.1 : ℂ) * (suzukiTaExponentialL2 a 1 :
            SuzukiApertureInterval a.1 → ℂ) x)
          ((g : SuzukiApertureInterval a.1 → ℂ) x)
      rw [show (suzukiTaExponentialL2 a 1 : SuzukiApertureInterval a.1 → ℂ) x =
          (Real.exp (x.1) : ℂ) by
        simpa [suzukiTaExponentialL2, suzukiTaExponentialContinuous] using hexp]
      simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
      simp
      ring

theorem deriv_suzukiCompactL2Fourier_zeroExtend_I_eq_positionInner
    (a : SuzukiPositiveAperture) (g : SuzukiApertureIntervalL2 a.1) :
    deriv (suzukiCompactL2Fourier a.1 (suzukiApertureZeroExtendL2 g)) I =
      I * inner ℂ
        (suzukiAperturePosition a (suzukiTaExponentialL2 a (-1))) g := by
  rw [(hasDerivAt_suzukiCompactL2Fourier a.2.le
    (suzukiApertureZeroExtendL2 g) I).deriv]
  rw [suzukiApertureZeroExtendL2_cutoff]
  have hzero := suzukiApertureZeroExtendL2_coeFn g
  calc
    (∫ x : ℝ, (suzukiApertureZeroExtendL2 g : ℝ → ℂ) x *
        (I * (x : ℂ)) * Complex.exp (I * I * (x : ℂ))) =
      ∫ x : ℝ, suzukiApertureZeroExtend g x *
        ((I * (x : ℂ)) * Complex.exp (I * I * (x : ℂ))) := by
          apply integral_congr_ae
          filter_upwards [hzero] with x hx
          rw [hx]
          ring
    _ = ∫ x : SuzukiApertureInterval a.1, (g : SuzukiApertureInterval a.1 → ℂ) x *
        ((I * (x.1 : ℂ)) * Complex.exp (I * I * (x.1 : ℂ))) :=
      integral_suzukiApertureZeroExtend_mul a.1 g _
    _ = I * inner ℂ
        (suzukiAperturePosition a (suzukiTaExponentialL2 a (-1))) g := by
      rw [MeasureTheory.L2.inner_def, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [suzukiAperturePosition_ae a (suzukiTaExponentialL2 a (-1)),
        ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
          (suzukiTaExponentialContinuous a (-1))] with x hpos hexp
      rw [hpos]
      change (g : SuzukiApertureInterval a.1 → ℂ) x *
          ((I * (x.1 : ℂ)) * Complex.exp (I * I * (x.1 : ℂ))) =
        I * inner ℂ
          ((x.1 : ℂ) * (suzukiTaExponentialL2 a (-1) :
            SuzukiApertureInterval a.1 → ℂ) x)
          ((g : SuzukiApertureInterval a.1 → ℂ) x)
      rw [show (suzukiTaExponentialL2 a (-1) : SuzukiApertureInterval a.1 → ℂ) x =
          (Real.exp (-x.1) : ℂ) by
        simpa [suzukiTaExponentialL2, suzukiTaExponentialContinuous] using hexp]
      simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
      simp
      ring

theorem deriv_suzukiTaPhysicalFourier_plus_negI_eq_positionInner
    (a : SuzukiPositiveAperture) :
    deriv (suzukiTaPhysicalFourier a (suzukiTaPlusDeficiency a)) (-I) =
      I * (‖suzukiTaRawDeficiency a 1‖ : ℂ) *
        inner ℂ
          (suzukiAperturePosition a (suzukiTaExponentialL2 a 1))
          (suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a 1)) := by
  change deriv (fun z => suzukiCompactL2Fourier a.1
    (suzukiApertureZeroExtendL2
      (suzukiTaPhysicalEmbedding a (suzukiTaPlusDeficiency a))) z) (-I) = _
  rw [suzukiTaPlusDeficiency, map_smul,
    suzukiTaPhysicalEmbedding_rawDeficiency_eq_covariance,
    norm_suzukiTaRawDeficiency_neg_eq a 1,
    deriv_suzukiCompactL2Fourier_zeroExtend_negI_eq_positionInner,
    inner_smul_right]
  ring

theorem deriv_suzukiTaPhysicalFourier_plus_I_eq_positionInner
    (a : SuzukiPositiveAperture) :
    deriv (suzukiTaPhysicalFourier a (suzukiTaPlusDeficiency a)) I =
      I * (‖suzukiTaRawDeficiency a 1‖ : ℂ) *
        inner ℂ
          (suzukiAperturePosition a (suzukiTaExponentialL2 a (-1)))
          (suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a 1)) := by
  change deriv (fun z => suzukiCompactL2Fourier a.1
    (suzukiApertureZeroExtendL2
      (suzukiTaPhysicalEmbedding a (suzukiTaPlusDeficiency a))) z) I = _
  rw [suzukiTaPlusDeficiency, map_smul,
    suzukiTaPhysicalEmbedding_rawDeficiency_eq_covariance,
    norm_suzukiTaRawDeficiency_neg_eq a 1,
    deriv_suzukiCompactL2Fourier_zeroExtend_I_eq_positionInner,
    inner_smul_right]
  ring

@[simp] theorem suzukiWeilIntervalReflection_coshVecC_one
    (a : SuzukiPositiveAperture) :
    suzukiWeilIntervalReflection a
        ((suzukiApertureCoordinate a.2.le).coshVecC 1) =
      (suzukiApertureCoordinate a.2.le).coshVecC 1 := by
  have hc :
      (suzukiApertureCoordinate a.2.le).coshVecC 1 =
        (2 : ℂ)⁻¹ •
          (suzukiTaExponentialL2 a 1 + suzukiTaExponentialL2 a (-1)) := by
    rw [suzukiTaExponentialL2_eq_cosh_add_sinh,
      suzukiTaExponentialL2_neg_eq_cosh_sub_sinh]
    norm_num
    module
  rw [hc, map_smul, map_add,
    suzukiWeilIntervalReflection_exponential,
    suzukiWeilIntervalReflection_exponential]
  norm_num
  module

@[simp] theorem suzukiWeilIntervalReflection_sinhVecC_one
    (a : SuzukiPositiveAperture) :
    suzukiWeilIntervalReflection a
        ((suzukiApertureCoordinate a.2.le).sinhVecC 1) =
      -(suzukiApertureCoordinate a.2.le).sinhVecC 1 := by
  have hs :
      (suzukiApertureCoordinate a.2.le).sinhVecC 1 =
        (2 : ℂ)⁻¹ •
          (suzukiTaExponentialL2 a 1 - suzukiTaExponentialL2 a (-1)) := by
    rw [suzukiTaExponentialL2_eq_cosh_add_sinh,
      suzukiTaExponentialL2_neg_eq_cosh_sub_sinh]
    norm_num
    module
  rw [hs, map_smul, map_sub,
    suzukiWeilIntervalReflection_exponential,
    suzukiWeilIntervalReflection_exponential]
  norm_num
  module

@[simp] theorem suzukiWeilIntervalReflection_position_coshVecC_one
    (a : SuzukiPositiveAperture) :
    suzukiWeilIntervalReflection a
        (suzukiAperturePosition a
          ((suzukiApertureCoordinate a.2.le).coshVecC 1)) =
      -suzukiAperturePosition a
          ((suzukiApertureCoordinate a.2.le).coshVecC 1) := by
  rw [suzukiWeilIntervalReflection_position_anticommute,
    suzukiWeilIntervalReflection_coshVecC_one]

@[simp] theorem suzukiWeilIntervalReflection_position_sinhVecC_one
    (a : SuzukiPositiveAperture) :
    suzukiWeilIntervalReflection a
        (suzukiAperturePosition a
          ((suzukiApertureCoordinate a.2.le).sinhVecC 1)) =
      suzukiAperturePosition a
          ((suzukiApertureCoordinate a.2.le).sinhVecC 1) := by
  rw [suzukiWeilIntervalReflection_position_anticommute,
    suzukiWeilIntervalReflection_sinhVecC_one, map_neg, neg_neg]

@[simp] theorem suzukiWeilIntervalReflection_covariance_coshVecC_one
    (a : SuzukiPositiveAperture) :
    suzukiWeilIntervalReflection a
        (suzukiWeilIntervalCovariance a
          ((suzukiApertureCoordinate a.2.le).coshVecC 1)) =
      suzukiWeilIntervalCovariance a
        ((suzukiApertureCoordinate a.2.le).coshVecC 1) := by
  rw [← suzukiWeilIntervalCovariance_reflection,
    suzukiWeilIntervalReflection_coshVecC_one]

@[simp] theorem suzukiWeilIntervalReflection_covariance_sinhVecC_one
    (a : SuzukiPositiveAperture) :
    suzukiWeilIntervalReflection a
        (suzukiWeilIntervalCovariance a
          ((suzukiApertureCoordinate a.2.le).sinhVecC 1)) =
      -suzukiWeilIntervalCovariance a
        ((suzukiApertureCoordinate a.2.le).sinhVecC 1) := by
  rw [← suzukiWeilIntervalCovariance_reflection,
    suzukiWeilIntervalReflection_sinhVecC_one, map_neg]

theorem inner_positionCosh_covarianceCosh_eq_zero
    (a : SuzukiPositiveAperture) :
    inner ℂ
        (suzukiAperturePosition a
          ((suzukiApertureCoordinate a.2.le).coshVecC 1))
        (suzukiWeilIntervalCovariance a
          ((suzukiApertureCoordinate a.2.le).coshVecC 1)) = 0 := by
  let u := suzukiAperturePosition a
    ((suzukiApertureCoordinate a.2.le).coshVecC 1)
  let v := suzukiWeilIntervalCovariance a
    ((suzukiApertureCoordinate a.2.le).coshVecC 1)
  have hmap := (suzukiWeilIntervalReflection a).inner_map_map u v
  have hu : suzukiWeilIntervalReflection a u = -u := by
    exact suzukiWeilIntervalReflection_position_coshVecC_one a
  have hv : suzukiWeilIntervalReflection a v = v := by
    exact suzukiWeilIntervalReflection_covariance_coshVecC_one a
  rw [hu, hv, inner_neg_left] at hmap
  linear_combination -hmap / 2

theorem inner_positionSinh_covarianceSinh_eq_zero
    (a : SuzukiPositiveAperture) :
    inner ℂ
        (suzukiAperturePosition a
          ((suzukiApertureCoordinate a.2.le).sinhVecC 1))
        (suzukiWeilIntervalCovariance a
          ((suzukiApertureCoordinate a.2.le).sinhVecC 1)) = 0 := by
  let u := suzukiAperturePosition a
    ((suzukiApertureCoordinate a.2.le).sinhVecC 1)
  let v := suzukiWeilIntervalCovariance a
    ((suzukiApertureCoordinate a.2.le).sinhVecC 1)
  have hmap := (suzukiWeilIntervalReflection a).inner_map_map u v
  have hu : suzukiWeilIntervalReflection a u = u := by
    exact suzukiWeilIntervalReflection_position_sinhVecC_one a
  have hv : suzukiWeilIntervalReflection a v = -v := by
    exact suzukiWeilIntervalReflection_covariance_sinhVecC_one a
  rw [hu, hv, inner_neg_right] at hmap
  linear_combination -hmap / 2

/-- Actual even-channel endpoint tilt, before scalarization. -/
def suzukiTaV2ActualEvenTilt (a : SuzukiPositiveAperture) : ℂ :=
  (‖suzukiTaRawDeficiency a 1‖ : ℂ) *
    inner ℂ
      (suzukiAperturePosition a
        ((suzukiApertureCoordinate a.2.le).sinhVecC 1))
      (suzukiWeilIntervalCovariance a
        ((suzukiApertureCoordinate a.2.le).coshVecC 1))

/-- Actual odd-channel endpoint tilt, before scalarization. -/
def suzukiTaV2ActualOddTilt (a : SuzukiPositiveAperture) : ℂ :=
  (‖suzukiTaRawDeficiency a 1‖ : ℂ) *
    inner ℂ
      (suzukiAperturePosition a
        ((suzukiApertureCoordinate a.2.le).coshVecC 1))
      (suzukiWeilIntervalCovariance a
        ((suzukiApertureCoordinate a.2.le).sinhVecC 1))

def suzukiTaV2ActualEvenEnergy (a : SuzukiPositiveAperture) : ℝ :=
  ‖suzukiTaRawDeficiency a 1‖ * suzukiTaCoalescingEvenEnergy a 1

def suzukiTaV2ActualOddEnergy (a : SuzukiPositiveAperture) : ℝ :=
  ‖suzukiTaRawDeficiency a 1‖ * suzukiTaCoalescingOddEnergy a 1

theorem deriv_suzukiTaPhysicalFourier_plus_negI_eq_actualTilts
    (a : SuzukiPositiveAperture) :
    deriv (suzukiTaPhysicalFourier a (suzukiTaPlusDeficiency a)) (-I) =
      I * (suzukiTaV2ActualEvenTilt a + suzukiTaV2ActualOddTilt a) := by
  rw [deriv_suzukiTaPhysicalFourier_plus_negI_eq_positionInner,
    suzukiTaExponentialL2_eq_cosh_add_sinh,
    map_add, map_add, inner_add_left, inner_add_right,
    inner_add_right, inner_positionCosh_covarianceCosh_eq_zero,
    inner_positionSinh_covarianceSinh_eq_zero,
    suzukiTaV2ActualEvenTilt, suzukiTaV2ActualOddTilt]
  ring

theorem deriv_suzukiTaPhysicalFourier_plus_I_eq_actualTilts
    (a : SuzukiPositiveAperture) :
    deriv (suzukiTaPhysicalFourier a (suzukiTaPlusDeficiency a)) I =
      I * (suzukiTaV2ActualOddTilt a - suzukiTaV2ActualEvenTilt a) := by
  rw [deriv_suzukiTaPhysicalFourier_plus_I_eq_positionInner,
    suzukiTaExponentialL2_neg_eq_cosh_sub_sinh,
    suzukiTaExponentialL2_eq_cosh_add_sinh,
    map_sub, map_add, inner_sub_left, inner_add_right,
    inner_add_right, inner_positionCosh_covarianceCosh_eq_zero,
    inner_positionSinh_covarianceSinh_eq_zero,
    suzukiTaV2ActualEvenTilt, suzukiTaV2ActualOddTilt]
  ring

/-- Exact complex parity curvature of the actual completed covariance source. -/
theorem suzukiTaV2EndpointSecondTorque_eq_actualParityCurvature
    (a : SuzukiPositiveAperture) :
    suzukiTaV2EndpointSecondTorque a =
      8 *
        (suzukiTaV2ActualEvenTilt a * (suzukiTaV2ActualOddEnergy a : ℂ) -
          suzukiTaV2ActualOddTilt a * (suzukiTaV2ActualEvenEnergy a : ℂ)) /
        ((suzukiTaV2ActualEvenEnergy a : ℂ) +
          (suzukiTaV2ActualOddEnergy a : ℂ)) ^ (2 : ℕ) := by
  rw [suzukiTaV2EndpointSecondTorque,
    deriv_suzukiTaPhysicalFourier_plus_I_eq_actualTilts,
    deriv_suzukiTaPhysicalFourier_plus_negI_eq_actualTilts,
    physicalFourier_plus_I_eq_scaled_energy_sub,
    physicalFourier_plus_negI_eq_scaled_energy_add,
    suzukiTaV2ActualEvenEnergy, suzukiTaV2ActualOddEnergy]
  push_cast
  ring_nf
  rw [I_sq]
  ring

end RHTower
end
