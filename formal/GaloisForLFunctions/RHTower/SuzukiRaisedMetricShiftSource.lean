import GaloisForLFunctions.RHTower.SuzukiTaV2ActualBoundarySourceLaw
import GaloisForLFunctions.RHTower.SuzukiTaV2RawSourceProfile

open Complex Filter
open scoped Topology InnerProduct NNReal
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- The shift increment acts on the actual interval covariance. -/
def suzukiRaisedMetricTransfer (a : SuzukiPositiveAperture) (t : ℝ≥0) :
    SuzukiApertureIntervalL2 a.1 →L[ℂ] SuzukiApertureIntervalL2 a.1 :=
  1 + ((t : ℝ) : ℂ) • suzukiWeilIntervalCovariance a

private theorem transfer_coercive (a : SuzukiPositiveAperture) (t : ℝ≥0)
    (v : SuzukiApertureIntervalL2 a.1) :
    ‖v‖ ^ 2 ≤ (inner ℂ (suzukiRaisedMetricTransfer a t v) v).re := by
  have hp := (suzukiWeilIntervalCovariance_isPositive a).re_inner_nonneg_left v
  change 0 ≤ (inner ℂ (suzukiWeilIntervalCovariance a v) v).re at hp
  simp only [suzukiRaisedMetricTransfer, add_apply,
    one_apply_eq_self, smul_apply,
    inner_add_left, inner_smul_left, Complex.conj_ofReal,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, inner_self_eq_norm_sq_to_K]
  norm_cast
  exact le_add_of_nonneg_right (mul_nonneg t.2 hp)

private theorem transfer_norm_lower (a : SuzukiPositiveAperture) (t : ℝ≥0)
    (v : SuzukiApertureIntervalL2 a.1) :
    ‖v‖ ≤ ‖suzukiRaisedMetricTransfer a t v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  have hp := transfer_coercive a t v
  have hb := re_inner_le_norm (𝕜 := ℂ) (suzukiRaisedMetricTransfer a t v) v
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  change (inner ℂ (suzukiRaisedMetricTransfer a t v) v).re ≤ _ at hb
  nlinarith

theorem suzukiRaisedMetricTransfer_isUnit (a : SuzukiPositiveAperture) (t : ℝ≥0) :
    IsUnit (suzukiRaisedMetricTransfer a t) := by
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _ (c := 1) zero_lt_one
  intro v
  simpa only [NNReal.coe_one, mul_one] using
    (transfer_coercive a t v).trans (Complex.re_le_norm _)

/-- Exact inverse of the positive transfer, with existence discharged. -/
def suzukiRaisedMetricInverse (a : SuzukiPositiveAperture) (t : ℝ≥0) :
    SuzukiApertureIntervalL2 a.1 →L[ℂ] SuzukiApertureIntervalL2 a.1 :=
  ↑(suzukiRaisedMetricTransfer_isUnit a t).unit⁻¹

theorem suzukiRaisedMetricTransfer_inverse_apply
    (a : SuzukiPositiveAperture) (t : ℝ≥0) (v : SuzukiApertureIntervalL2 a.1) :
    suzukiRaisedMetricTransfer a t (suzukiRaisedMetricInverse a t v) = v := by
  have h := congrArg (fun T : SuzukiApertureIntervalL2 a.1 →L[ℂ]
      SuzukiApertureIntervalL2 a.1 => T v)
    (suzukiRaisedMetricTransfer_isUnit a t).mul_val_inv
  exact h

theorem norm_suzukiRaisedMetricInverse_apply_le
    (a : SuzukiPositiveAperture) (t : ℝ≥0) (v : SuzukiApertureIntervalL2 a.1) :
    ‖suzukiRaisedMetricInverse a t v‖ ≤ ‖v‖ := by
  simpa only [suzukiRaisedMetricTransfer_inverse_apply] using
    transfer_norm_lower a t (suzukiRaisedMetricInverse a t v)

def suzukiRaisedMetricShift (a : SuzukiPositiveAperture) (t : ℝ≥0) : ℝ :=
  boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) + t

def suzukiRaisedMetricCovariance (a : SuzukiPositiveAperture) (t : ℝ≥0) :
    SuzukiApertureIntervalL2 a.1 →L[ℂ] SuzukiApertureIntervalL2 a.1 :=
  suzukiWeilIntervalCovariance a * suzukiRaisedMetricInverse a t

/-- The new response solves the raised-shift equation of the same actual
Friedrichs operator. No inverse equation is assumed. -/
theorem suzukiRaisedMetricCovariance_shiftEquation
    (a : SuzukiPositiveAperture) (t : ℝ≥0) (p : SuzukiApertureIntervalL2 a.1) :
    suzukiWeilFriedrichsOperator a
        (suzukiWeilIntervalCovarianceDomain a (suzukiRaisedMetricInverse a t p)) +
      (suzukiRaisedMetricShift a t : ℂ) • suzukiRaisedMetricCovariance a t p = p := by
  have hb := suzukiWeilIntervalCovariance_shiftEquation a (suzukiRaisedMetricInverse a t p)
  have ht := suzukiRaisedMetricTransfer_inverse_apply a t p
  change suzukiRaisedMetricInverse a t p +
    ((t : ℝ) : ℂ) • suzukiRaisedMetricCovariance a t p = p at ht
  rw [suzukiRaisedMetricShift, Complex.ofReal_add, add_smul]
  change _ + ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) •
    suzukiWeilIntervalCovariance a (suzukiRaisedMetricInverse a t p) + _) = _
  rw [← add_assoc, hb]
  exact ht

/-- Raising the metric shift contracts the normalized source defect, for
every physical source and every nonnegative increment. -/
theorem norm_suzukiRaisedMetric_source_defect_le
    (a : SuzukiPositiveAperture) (t : ℝ≥0) (p : SuzukiApertureIntervalL2 a.1) :
    ‖(suzukiRaisedMetricShift a t : ℂ) • suzukiRaisedMetricCovariance a t p - p‖ ≤
      ‖(boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) •
        suzukiWeilIntervalCovariance a p - p‖ := by
  have hc (v : SuzukiApertureIntervalL2 a.1) :
      suzukiRaisedMetricTransfer a t (suzukiWeilIntervalCovariance a v) =
        suzukiWeilIntervalCovariance a (suzukiRaisedMetricTransfer a t v) := by
    simp only [suzukiRaisedMetricTransfer, add_apply,
      one_apply_eq_self, smul_apply, map_add, map_smul]
  have hid : suzukiRaisedMetricTransfer a t
      ((suzukiRaisedMetricShift a t : ℂ) • suzukiRaisedMetricCovariance a t p - p) =
      (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) •
        suzukiWeilIntervalCovariance a p - p := by
    rw [map_sub, map_smul]
    change (suzukiRaisedMetricShift a t : ℂ) •
      suzukiRaisedMetricTransfer a t
        (suzukiWeilIntervalCovariance a (suzukiRaisedMetricInverse a t p)) - _ = _
    rw [hc, suzukiRaisedMetricTransfer_inverse_apply]
    simp only [suzukiRaisedMetricTransfer, add_apply,
      one_apply_eq_self, smul_apply,
      suzukiRaisedMetricShift, Complex.ofReal_add]
    module
  exact (transfer_norm_lower a t _).trans_eq (congrArg norm hid)

/-- The raised response remains a literal vector in the existing form domain. -/
def suzukiRaisedMetricRawDeficiency (a : SuzukiPositiveAperture) (t : ℝ≥0) :
    SuzukiTaHilbert a :=
  suzukiTaSourceResponse a ((suzukiApertureL2Equiv a)
    (suzukiRaisedMetricInverse a t (suzukiTaExponentialL2 a 1)))

theorem suzukiRaisedMetricRawDeficiency_physical
    (a : SuzukiPositiveAperture) (t : ℝ≥0) :
    suzukiTaPhysicalEmbedding a (suzukiRaisedMetricRawDeficiency a t) =
      suzukiRaisedMetricCovariance a t (suzukiTaExponentialL2 a 1) := by
  rw [suzukiRaisedMetricRawDeficiency, suzukiTaPhysicalEmbedding_sourceResponse,
    (suzukiApertureL2Equiv a).symm_apply_apply]
  rfl

theorem suzukiRaisedMetricRawDeficiency_zero (a : SuzukiPositiveAperture) :
    suzukiRaisedMetricRawDeficiency a 0 = suzukiTaRawDeficiency a 1 := by
  have hi (v : SuzukiApertureIntervalL2 a.1) : suzukiRaisedMetricInverse a 0 v = v := by
    simpa [suzukiRaisedMetricTransfer] using suzukiRaisedMetricTransfer_inverse_apply a 0 v
  rw [suzukiRaisedMetricRawDeficiency, hi]
  have hp : (suzukiApertureL2Equiv a) (suzukiTaExponentialL2 a 1) =
      ccmPolarApertureVector a 1 := by
    apply Subtype.ext
    exact suzukiApertureZeroExtendL2_exponential_eq_ccmPolarL2Vector a 1
  rw [hp, suzukiTaSourceResponse_polar]

end RHTower
end
