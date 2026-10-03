import GaloisForLFunctions.RHTower.SuzukiSpectralMarginLimit

open Complex Filter
open scoped Topology InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- Prescribed covariance defect for the actual fixed exponential source. -/
def suzukiSpectralBaseDefect (a : SuzukiPositiveAperture) : SuzukiApertureIntervalL2 a.1 :=
  (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) •
    suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a 1) - suzukiTaExponentialL2 a 1

/-- Actual amplified defect, with the admissible metric shift retained. -/
def suzukiSpectralSourceDefect (b : SuzukiSpectralMarginParameters) :
    SuzukiApertureIntervalL2 b.1.1 :=
  (suzukiSpectralMarginShift b.1 b.2 : ℂ) •
    suzukiSpectralMarginCovariance b.1 b.2 (suzukiTaExponentialL2 b.1 1) -
      suzukiTaExponentialL2 b.1 1

/-- Covariance normalized at its actual top spectral value. -/
def suzukiSpectralNormalizedCovariance (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 →L[ℂ] SuzukiApertureIntervalL2 a.1 :=
  ((‖suzukiWeilIntervalCovariance a‖⁻¹ : ℝ) : ℂ) • suzukiWeilIntervalCovariance a

private theorem polar_equiv (a : SuzukiPositiveAperture) :
    (suzukiApertureL2Equiv a) (suzukiTaExponentialL2 a 1) = ccmPolarApertureVector a 1 := by
  apply Subtype.ext
  exact suzukiApertureZeroExtendL2_exponential_eq_ccmPolarL2Vector a 1

/-- The defect used in the Fourier pairing is exactly the physical image
of the actual interval source defect. -/
theorem suzukiSpectralSourceDefect_physical (b : SuzukiSpectralMarginParameters) :
    (suzukiApertureL2Equiv b.1) (suzukiSpectralSourceDefect b) =
      (suzukiSpectralMarginShift b.1 b.2 : ℂ) • suzukiSpectralMarginPhysical b.1 b.2 -
        ccmPolarApertureVector b.1 1 := by
  have hf : (suzukiApertureL2Equiv b.1)
      (suzukiSpectralMarginCovariance b.1 b.2 (suzukiTaExponentialL2 b.1 1)) =
      suzukiSpectralMarginPhysical b.1 b.2 := by
    rw [← suzukiSpectralMarginRawDeficiency_physical]
    change (suzukiApertureL2Equiv b.1) ((suzukiApertureL2Equiv b.1).symm _) = _
    rw [(suzukiApertureL2Equiv b.1).apply_symm_apply]
    rfl
  rw [suzukiSpectralSourceDefect, map_sub, map_smul, hf, polar_equiv]

/-- Exact source amplification equation, before taking any norm. -/
theorem suzukiSpectralSourceDefect_transfer (b : SuzukiSpectralMarginParameters) :
    suzukiSpectralMarginTransfer b.1 b.2 (suzukiSpectralSourceDefect b) =
      suzukiSpectralBaseDefect b.1 := by
  have hc (v : SuzukiApertureIntervalL2 b.1.1) :
      suzukiSpectralMarginTransfer b.1 b.2 (suzukiWeilIntervalCovariance b.1 v) =
        suzukiWeilIntervalCovariance b.1 (suzukiSpectralMarginTransfer b.1 b.2 v) := by
    simp only [suzukiSpectralMarginTransfer, add_apply, one_apply_eq_self,
      smul_apply, map_add, map_smul]
  rw [suzukiSpectralSourceDefect, map_sub, map_smul]
  change (suzukiSpectralMarginShift b.1 b.2 : ℂ) •
    suzukiSpectralMarginTransfer b.1 b.2
      (suzukiWeilIntervalCovariance b.1
        (suzukiSpectralMarginInverse b.1 b.2 (suzukiTaExponentialL2 b.1 1))) - _ = _
  rw [hc, suzukiSpectralMarginTransfer_inverse_apply]
  simp only [suzukiSpectralMarginTransfer, add_apply, one_apply_eq_self,
    smul_apply, suzukiSpectralMarginShift, Complex.ofReal_add, suzukiSpectralBaseDefect]
  module

theorem norm_suzukiSpectralNormalizedCovariance_apply_le (a : SuzukiPositiveAperture)
    (v : SuzukiApertureIntervalL2 a.1) :
    ‖suzukiSpectralNormalizedCovariance a v‖ ≤ ‖v‖ := by
  have hp := norm_suzukiWeilIntervalCovariance_pos a
  simp only [suzukiSpectralNormalizedCovariance, smul_apply, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  calc
    _ ≤ ‖suzukiWeilIntervalCovariance a‖⁻¹ *
        (‖suzukiWeilIntervalCovariance a‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left ((suzukiWeilIntervalCovariance a).le_opNorm v)
        (inv_nonneg.mpr hp.le)
    _ = ‖v‖ := by rw [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]

/-- Actual relative covariance residual is controlled by the base defect
and the exact relative spectral-floor margin. -/
theorem norm_suzukiSpectralSourceDefect_topResidual_le
    (b : SuzukiSpectralMarginParameters) :
    ‖suzukiSpectralSourceDefect b -
        suzukiSpectralNormalizedCovariance b.1 (suzukiSpectralSourceDefect b)‖ ≤
      ‖suzukiSpectralBaseDefect b.1‖ + b.2.1 * ‖suzukiSpectralSourceDefect b‖ := by
  have hid : suzukiSpectralSourceDefect b -
      suzukiSpectralNormalizedCovariance b.1 (suzukiSpectralSourceDefect b) =
      suzukiSpectralBaseDefect b.1 - (b.2.1 : ℂ) •
        suzukiSpectralNormalizedCovariance b.1 (suzukiSpectralSourceDefect b) := by
    rw [← suzukiSpectralSourceDefect_transfer b]
    simp only [suzukiSpectralNormalizedCovariance, suzukiSpectralMarginTransfer,
      smul_apply, add_apply, one_apply_eq_self, smul_smul]
    push_cast
    module
  rw [hid]
  apply (norm_sub_le _ _).trans
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos b.2.2]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (norm_suzukiSpectralNormalizedCovariance_apply_le b.1 _) b.2.2.le)

private theorem norm_base_eq_profile (a : SuzukiPositiveAperture) :
    ‖suzukiSpectralBaseDefect a‖ =
      boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) *
        ‖ccmArchimedeanFormToAperture a
          (suzukiTaToFormCLM a (suzukiTaRawDeficiency a 1)) -
            ccmSourceShiftProfile a (ccmPolarApertureVector a 1)‖ := by
  let e := suzukiApertureL2Equiv a
  let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)
  let f := ccmArchimedeanFormToAperture a
    (suzukiTaToFormCLM a (suzukiTaRawDeficiency a 1))
  have hc : 0 < c := boundedPerturbedFormShift_pos _
  have hf : e (suzukiWeilIntervalCovariance a (suzukiTaExponentialL2 a 1)) = f := by
    rw [← suzukiTaPhysicalEmbedding_rawDeficiency_eq_covariance]
    change e (e.symm _) = _
    rw [e.apply_symm_apply]
    rfl
  have hp : e (suzukiTaExponentialL2 a 1) = ccmPolarApertureVector a 1 := polar_equiv a
  rw [← e.norm_map (suzukiSpectralBaseDefect a)]
  simp only [suzukiSpectralBaseDefect, map_sub, map_smul, hf, hp]
  have hid : (c : ℂ) • f - ccmPolarApertureVector a 1 =
      (c : ℂ) • (f - ccmSourceShiftProfile a (ccmPolarApertureVector a 1)) := by
    change _ = (c : ℂ) • (f - (((c⁻¹ : ℝ) : ℂ) • ccmPolarApertureVector a 1))
    rw [smul_sub, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hc.ne',
      Complex.ofReal_one, one_smul]
  rw [hid, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]

/-- The actual base defect is negligible at the natural exponential source scale. -/
theorem tendsto_suzukiSpectralBaseDefect_scaled_norm :
    Tendsto (fun a : SuzukiPositiveAperture => Real.exp (-a.1) * ‖suzukiSpectralBaseDefect a‖)
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 0) := by
  let C := ‖ccmArchimedeanRemainderScalar‖ + 47
  have hlim := tendsto_suzukiTaV2_rawSource_profile_norm.const_mul C
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun a =>
    mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) ?_ hlim
  apply Eventually.of_forall
  intro a
  rw [norm_base_eq_profile, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    _ ≤ Real.exp (-a.1) * (C * Real.exp a.1) :=
      mul_le_mul_of_nonneg_left (suzukiWeilIntervalShift_le_exp a) (Real.exp_pos _).le
    _ = C := by rw [mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

end RHTower
end
