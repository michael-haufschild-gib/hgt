import GaloisForLFunctions.RHTower.SuzukiRaisedMetricShiftSource

open Complex Filter
open scoped Topology InnerProduct NNReal
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- Positive distance from the actual spectral floor, relative to the
prescribed floor distance. Every strictly admissible metric shift occurs. -/
abbrev SuzukiSpectralMargin := {m : ℝ // 0 < m}

def suzukiSpectralMarginWeight (m : SuzukiSpectralMargin) : ℝ := min 1 m.1

theorem suzukiSpectralMarginWeight_pos (m : SuzukiSpectralMargin) :
    0 < suzukiSpectralMarginWeight m := lt_min zero_lt_one m.2

def suzukiSpectralMarginShift (a : SuzukiPositiveAperture) (m : SuzukiSpectralMargin) : ℝ :=
  boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) +
    (m.1 - 1) / ‖suzukiWeilIntervalCovariance a‖

/-- Exact spectral coordinate, using the actual attained ground energy. -/
theorem suzukiSpectralMarginShift_relative_floor
    (a : SuzukiPositiveAperture) (m : SuzukiSpectralMargin) :
    (suzukiWeilIntervalGroundEnergy a + suzukiSpectralMarginShift a m) /
      (suzukiWeilIntervalGroundEnergy a +
        boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)) = m.1 := by
  have h := (norm_suzukiWeilIntervalCovariance_pos a).ne'
  simp only [suzukiWeilIntervalGroundEnergy, suzukiSpectralMarginShift]
  field_simp
  ring

/-- The shifted floor is strictly positive and has the exact relative size. -/
theorem suzukiSpectralMarginShift_floor_gap
    (a : SuzukiPositiveAperture) (m : SuzukiSpectralMargin) :
    suzukiWeilIntervalGroundEnergy a + suzukiSpectralMarginShift a m =
      m.1 / ‖suzukiWeilIntervalCovariance a‖ := by
  simp only [suzukiWeilIntervalGroundEnergy, suzukiSpectralMarginShift]
  ring

/-- These coordinates exhaust, rather than assume, strict admissibility. -/
theorem range_suzukiSpectralMarginShift (a : SuzukiPositiveAperture) :
    Set.range (suzukiSpectralMarginShift a) = Set.Ioi (-suzukiWeilIntervalGroundEnergy a) := by
  ext d
  constructor
  · rintro ⟨m, rfl⟩
    have hp := div_pos m.2 (norm_suzukiWeilIntervalCovariance_pos a)
    rw [← suzukiSpectralMarginShift_floor_gap] at hp
    change -suzukiWeilIntervalGroundEnergy a < suzukiSpectralMarginShift a m
    linarith
  · intro hd
    have hmu := norm_suzukiWeilIntervalCovariance_pos a
    have hg : 0 < suzukiWeilIntervalGroundEnergy a + d := by
      change -suzukiWeilIntervalGroundEnergy a < d at hd
      linarith
    let m : SuzukiSpectralMargin :=
      ⟨(suzukiWeilIntervalGroundEnergy a + d) * ‖suzukiWeilIntervalCovariance a‖,
        mul_pos hg hmu⟩
    refine ⟨m, ?_⟩
    have he := suzukiSpectralMarginShift_floor_gap a m
    dsimp [m] at he
    rw [mul_div_cancel_right₀ _ hmu.ne'] at he
    linarith

/-- The transfer acts on the same physical interval space as the original covariance. -/
def suzukiSpectralMarginTransfer (a : SuzukiPositiveAperture) (m : SuzukiSpectralMargin) :
    SuzukiApertureIntervalL2 a.1 →L[ℂ] SuzukiApertureIntervalL2 a.1 :=
  1 + (((m.1 - 1) / ‖suzukiWeilIntervalCovariance a‖ : ℝ) : ℂ) •
    suzukiWeilIntervalCovariance a

private theorem transfer_coercive (a : SuzukiPositiveAperture) (m : SuzukiSpectralMargin)
    (v : SuzukiApertureIntervalL2 a.1) :
    suzukiSpectralMarginWeight m * ‖v‖ ^ 2 ≤
      (inner ℂ (suzukiSpectralMarginTransfer a m v) v).re := by
  let mu := ‖suzukiWeilIntervalCovariance a‖
  let h := (inner ℂ (suzukiWeilIntervalCovariance a v) v).re
  have hmu : 0 < mu := norm_suzukiWeilIntervalCovariance_pos a
  have hp : 0 ≤ h := (suzukiWeilIntervalCovariance_isPositive a).re_inner_nonneg_left v
  have hb : h ≤ mu * ‖v‖ ^ 2 := by
    calc
      h ≤ ‖suzukiWeilIntervalCovariance a v‖ * ‖v‖ := re_inner_le_norm (𝕜 := ℂ) _ _
      _ ≤ (mu * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right ((suzukiWeilIntervalCovariance a).le_opNorm v) (norm_nonneg _)
      _ = _ := by ring
  have hrp : 0 ≤ h / mu := div_nonneg hp hmu.le
  have hrb : h / mu ≤ ‖v‖ ^ 2 := (div_le_iff₀ hmu).2 (by nlinarith [hb])
  have heq : (inner ℂ (suzukiSpectralMarginTransfer a m v) v).re =
      ‖v‖ ^ 2 + (m.1 - 1) * (h / mu) := by
    simp only [suzukiSpectralMarginTransfer, add_apply, one_apply_eq_self, smul_apply,
      inner_add_left, inner_smul_left, Complex.conj_ofReal, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      inner_self_eq_norm_sq_to_K]
    norm_cast
    dsimp [h, mu]
    ring
  rw [heq]
  rcases le_total 1 m.1 with hm | hm
  · rw [suzukiSpectralMarginWeight, min_eq_left hm]
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) hrp]
  · rw [suzukiSpectralMarginWeight, min_eq_right hm]
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hrb)]

private theorem transfer_norm_lower (a : SuzukiPositiveAperture) (m : SuzukiSpectralMargin)
    (v : SuzukiApertureIntervalL2 a.1) :
    suzukiSpectralMarginWeight m * ‖v‖ ≤ ‖suzukiSpectralMarginTransfer a m v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  have hp := transfer_coercive a m v
  have hb := re_inner_le_norm (𝕜 := ℂ) (suzukiSpectralMarginTransfer a m v) v
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  change (inner ℂ (suzukiSpectralMarginTransfer a m v) v).re ≤ _ at hb
  nlinarith

theorem suzukiSpectralMarginTransfer_isUnit (a : SuzukiPositiveAperture)
    (m : SuzukiSpectralMargin) : IsUnit (suzukiSpectralMarginTransfer a m) := by
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _
    (c := ⟨suzukiSpectralMarginWeight m, (suzukiSpectralMarginWeight_pos m).le⟩)
    (suzukiSpectralMarginWeight_pos m)
  intro v
  change ‖v‖ ^ 2 * suzukiSpectralMarginWeight m ≤ _
  simpa only [mul_comm] using (transfer_coercive a m v).trans (Complex.re_le_norm _)

def suzukiSpectralMarginInverse (a : SuzukiPositiveAperture) (m : SuzukiSpectralMargin) :
    SuzukiApertureIntervalL2 a.1 →L[ℂ] SuzukiApertureIntervalL2 a.1 :=
  ↑(suzukiSpectralMarginTransfer_isUnit a m).unit⁻¹

theorem suzukiSpectralMarginTransfer_inverse_apply
    (a : SuzukiPositiveAperture) (m : SuzukiSpectralMargin) (v : SuzukiApertureIntervalL2 a.1) :
    suzukiSpectralMarginTransfer a m (suzukiSpectralMarginInverse a m v) = v := by
  exact congrArg (fun T : SuzukiApertureIntervalL2 a.1 →L[ℂ]
    SuzukiApertureIntervalL2 a.1 => T v) (suzukiSpectralMarginTransfer_isUnit a m).mul_val_inv

def suzukiSpectralMarginCovariance (a : SuzukiPositiveAperture) (m : SuzukiSpectralMargin) :
    SuzukiApertureIntervalL2 a.1 →L[ℂ] SuzukiApertureIntervalL2 a.1 :=
  suzukiWeilIntervalCovariance a * suzukiSpectralMarginInverse a m

/-- The constructed response solves the actual operator's source equation
at every shift strictly above its floor; no inverse premise is imported. -/
theorem suzukiSpectralMarginCovariance_shiftEquation
    (a : SuzukiPositiveAperture) (m : SuzukiSpectralMargin) (p : SuzukiApertureIntervalL2 a.1) :
    suzukiWeilFriedrichsOperator a
        (suzukiWeilIntervalCovarianceDomain a (suzukiSpectralMarginInverse a m p)) +
      (suzukiSpectralMarginShift a m : ℂ) • suzukiSpectralMarginCovariance a m p = p := by
  have hb := suzukiWeilIntervalCovariance_shiftEquation a (suzukiSpectralMarginInverse a m p)
  have ht := suzukiSpectralMarginTransfer_inverse_apply a m p
  change suzukiSpectralMarginInverse a m p +
    (((m.1 - 1) / ‖suzukiWeilIntervalCovariance a‖ : ℝ) : ℂ) •
      suzukiSpectralMarginCovariance a m p = p at ht
  rw [suzukiSpectralMarginShift, Complex.ofReal_add, add_smul]
  change _ + ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) •
    suzukiWeilIntervalCovariance a (suzukiSpectralMarginInverse a m p) + _) = _
  rw [← add_assoc, hb]
  exact ht

/-- Margin-weighted source defects are dominated by the already audited
prescribed source defect, uniformly over all strictly admissible shifts. -/
theorem suzukiSpectralMargin_weighted_source_defect_le
    (a : SuzukiPositiveAperture) (m : SuzukiSpectralMargin) (p : SuzukiApertureIntervalL2 a.1) :
    suzukiSpectralMarginWeight m *
      ‖(suzukiSpectralMarginShift a m : ℂ) • suzukiSpectralMarginCovariance a m p - p‖ ≤
      ‖(boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) •
        suzukiWeilIntervalCovariance a p - p‖ := by
  have hc (v : SuzukiApertureIntervalL2 a.1) :
      suzukiSpectralMarginTransfer a m (suzukiWeilIntervalCovariance a v) =
        suzukiWeilIntervalCovariance a (suzukiSpectralMarginTransfer a m v) := by
    simp only [suzukiSpectralMarginTransfer, add_apply, one_apply_eq_self,
      smul_apply, map_add, map_smul]
  have hid : suzukiSpectralMarginTransfer a m
      ((suzukiSpectralMarginShift a m : ℂ) • suzukiSpectralMarginCovariance a m p - p) =
      (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) •
        suzukiWeilIntervalCovariance a p - p := by
    rw [map_sub, map_smul]
    change (suzukiSpectralMarginShift a m : ℂ) •
      suzukiSpectralMarginTransfer a m
        (suzukiWeilIntervalCovariance a (suzukiSpectralMarginInverse a m p)) - _ = _
    rw [hc, suzukiSpectralMarginTransfer_inverse_apply]
    simp only [suzukiSpectralMarginTransfer, add_apply, one_apply_eq_self, smul_apply,
      suzukiSpectralMarginShift, Complex.ofReal_add]
    module
  exact (transfer_norm_lower a m _).trans_eq (congrArg norm hid)

def suzukiSpectralMarginRawDeficiency (a : SuzukiPositiveAperture) (m : SuzukiSpectralMargin) :
    SuzukiTaHilbert a :=
  suzukiTaSourceResponse a ((suzukiApertureL2Equiv a)
    (suzukiSpectralMarginInverse a m (suzukiTaExponentialL2 a 1)))

theorem suzukiSpectralMarginRawDeficiency_physical
    (a : SuzukiPositiveAperture) (m : SuzukiSpectralMargin) :
    suzukiTaPhysicalEmbedding a (suzukiSpectralMarginRawDeficiency a m) =
      suzukiSpectralMarginCovariance a m (suzukiTaExponentialL2 a 1) := by
  rw [suzukiSpectralMarginRawDeficiency, suzukiTaPhysicalEmbedding_sourceResponse,
    (suzukiApertureL2Equiv a).symm_apply_apply]
  rfl

end RHTower
end
