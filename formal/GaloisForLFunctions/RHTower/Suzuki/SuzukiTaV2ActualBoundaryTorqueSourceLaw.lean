import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaV2ActualBoundarySourceLaw
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaV2ActualSecondDefectBound
import GaloisForLFunctions.HTGeometry.HyperbolicModulus

/-!
# Actual Suzuki torque in completed-source coordinates

The even and odd endpoint-renormalized source laws are coupled with exactly Suzuki's torque
weights. Their individually large boundary coefficients then enter only through

`a * tanh a - a * coth a = -a / (sinh a * cosh a)`.

Thus parity scalarization does not discard the boundary term: it turns it into an explicit
negative anomaly bounded by `2a / (sinh a * cosh a)`, which vanishes exponentially. The remaining
torque is an exact signed combination of two literal `ccmRestrictedWeilForm` cross terms. No
abstract domain premise or absolute-value separation of prime, polar, and Gamma pieces is used.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

theorem inner_cosh_covariance_cosh_eq_coalescingEvenEnergy
    (a : SuzukiPositiveAperture) :
    inner ℂ ((suzukiApertureCoordinate a.2.le).coshVecC 1)
        (suzukiWeilIntervalCovariance a
          ((suzukiApertureCoordinate a.2.le).coshVecC 1)) =
      (suzukiTaCoalescingEvenEnergy a 1 : ℂ) := by
  let v := (suzukiApertureCoordinate a.2.le).coshVecC 1
  have hsym := (suzukiWeilIntervalCovariance_isPositive a).inner_left_eq_inner_right v v
  have hconj :
      (starRingEnd ℂ) (inner ℂ v (suzukiWeilIntervalCovariance a v)) =
        inner ℂ v (suzukiWeilIntervalCovariance a v) := by
    rw [inner_conj_symm]
    exact hsym
  have hreal := (Complex.conj_eq_iff_re.mp hconj).symm
  calc
    inner ℂ ((suzukiApertureCoordinate a.2.le).coshVecC 1)
        (suzukiWeilIntervalCovariance a
          ((suzukiApertureCoordinate a.2.le).coshVecC 1)) =
      ((inner ℂ v (suzukiWeilIntervalCovariance a v)).re : ℂ) := hreal
    _ = (suzukiTaCoalescingEvenEnergy a 1 : ℂ) := by
      rfl

theorem inner_sinh_covariance_sinh_eq_coalescingOddEnergy
    (a : SuzukiPositiveAperture) :
    inner ℂ ((suzukiApertureCoordinate a.2.le).sinhVecC 1)
        (suzukiWeilIntervalCovariance a
          ((suzukiApertureCoordinate a.2.le).sinhVecC 1)) =
      (suzukiTaCoalescingOddEnergy a 1 : ℂ) := by
  let v := (suzukiApertureCoordinate a.2.le).sinhVecC 1
  have hsym := (suzukiWeilIntervalCovariance_isPositive a).inner_left_eq_inner_right v v
  have hconj :
      (starRingEnd ℂ) (inner ℂ v (suzukiWeilIntervalCovariance a v)) =
        inner ℂ v (suzukiWeilIntervalCovariance a v) := by
    rw [inner_conj_symm]
    exact hsym
  have hreal := (Complex.conj_eq_iff_re.mp hconj).symm
  calc
    inner ℂ ((suzukiApertureCoordinate a.2.le).sinhVecC 1)
        (suzukiWeilIntervalCovariance a
          ((suzukiApertureCoordinate a.2.le).sinhVecC 1)) =
      ((inner ℂ v (suzukiWeilIntervalCovariance a v)).re : ℂ) := hreal
    _ = (suzukiTaCoalescingOddEnergy a 1 : ℂ) := by
      rfl

theorem suzukiTaV2BoundaryCoefficient_sub_eq
    (a : SuzukiPositiveAperture) :
    suzukiTaV2EvenBoundaryCoefficient a - suzukiTaV2OddBoundaryCoefficient a =
      -a.1 / (Real.sinh a.1 * Real.cosh a.1) := by
  rw [suzukiTaV2EvenBoundaryCoefficient, suzukiTaV2OddBoundaryCoefficient,
    Real.tanh_eq_sinh_div_cosh]
  have hs : Real.sinh a.1 ≠ 0 := (Real.sinh_pos_iff.mpr a.property).ne'
  have hc : Real.cosh a.1 ≠ 0 := (Real.cosh_pos a.1).ne'
  field_simp
  have htrig : Real.sinh a.1 ^ (2 : ℕ) - Real.cosh a.1 ^ (2 : ℕ) = -1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq a.1]
  rw [htrig]
  ring

def suzukiTaV2ActualEvenBoundarySource (a : SuzukiPositiveAperture) : ℂ :=
  inner ℂ (suzukiTaV2EvenBoundary a)
      ((suzukiApertureCoordinate a.2.le).coshVecC 1) -
    (starRingEnd ℂ)
      (ccmRestrictedWeilForm a
        (suzukiTaV2ActualEvenResponseFormVector a)
        (suzukiTaV2EvenBoundaryFormVector a))

def suzukiTaV2ActualOddBoundarySource (a : SuzukiPositiveAperture) : ℂ :=
  inner ℂ (suzukiTaV2OddBoundary a)
      ((suzukiApertureCoordinate a.2.le).sinhVecC 1) -
    (starRingEnd ℂ)
      (ccmRestrictedWeilForm a
        (suzukiTaV2ActualOddResponseFormVector a)
        (suzukiTaV2OddBoundaryFormVector a))

def suzukiTaV2BoundaryTorqueAnomaly (a : SuzukiPositiveAperture) : ℂ :=
  8 *
    ((suzukiTaV2ActualEvenEnergy a : ℂ) *
      (suzukiTaV2ActualOddEnergy a : ℂ) *
      ((suzukiTaV2EvenBoundaryCoefficient a : ℂ) -
        (suzukiTaV2OddBoundaryCoefficient a : ℂ))) /
    ((suzukiTaV2ActualEvenEnergy a : ℂ) +
      (suzukiTaV2ActualOddEnergy a : ℂ)) ^ (2 : ℕ)

def suzukiTaV2ActualBoundarySourceTorque (a : SuzukiPositiveAperture) : ℂ :=
  8 * (‖suzukiTaRawDeficiency a 1‖ : ℂ) *
    (suzukiTaV2ActualEvenBoundarySource a *
        (suzukiTaV2ActualOddEnergy a : ℂ) -
      suzukiTaV2ActualOddBoundarySource a *
        (suzukiTaV2ActualEvenEnergy a : ℂ)) /
    ((suzukiTaV2ActualEvenEnergy a : ℂ) +
      (suzukiTaV2ActualOddEnergy a : ℂ)) ^ (2 : ℕ)

theorem suzukiTaV2ActualEvenEnergy_nonneg (a : SuzukiPositiveAperture) :
    0 ≤ suzukiTaV2ActualEvenEnergy a := by
  rw [suzukiTaV2ActualEvenEnergy,
    suzukiTaCoalescingEvenEnergy_eq_norm_sq]
  positivity

theorem suzukiTaV2ActualOddEnergy_nonneg (a : SuzukiPositiveAperture) :
    0 ≤ suzukiTaV2ActualOddEnergy a := by
  rw [suzukiTaV2ActualOddEnergy,
    suzukiTaCoalescingOddEnergy_eq_norm_sq]
  positivity

theorem suzukiTaV2ActualEnergy_add_pos (a : SuzukiPositiveAperture) :
    0 < suzukiTaV2ActualEvenEnergy a + suzukiTaV2ActualOddEnergy a := by
  have hn : 0 < ‖suzukiTaRawDeficiency a 1‖ :=
    norm_pos_iff.mpr (suzukiTaRawDeficiency_ne_zero a 1)
  have hs := suzukiTaCoalescingEnergy_add_eq_norm_sq a 1
  rw [suzukiTaV2ActualEvenEnergy, suzukiTaV2ActualOddEnergy]
  nlinarith [sq_pos_of_pos hn]

theorem suzukiTaV2ActualEnergy_add_ne_zero (a : SuzukiPositiveAperture) :
    (suzukiTaV2ActualEvenEnergy a : ℂ) +
        (suzukiTaV2ActualOddEnergy a : ℂ) ≠ 0 := by
  exact_mod_cast (suzukiTaV2ActualEnergy_add_pos a).ne'

theorem suzukiTaV2BoundaryTorqueAnomaly_eq
    (a : SuzukiPositiveAperture) :
    suzukiTaV2BoundaryTorqueAnomaly a =
      ((-(8 * a.1 * suzukiTaV2ActualEvenEnergy a *
          suzukiTaV2ActualOddEnergy a /
          ((Real.sinh a.1 * Real.cosh a.1) *
            (suzukiTaV2ActualEvenEnergy a +
              suzukiTaV2ActualOddEnergy a) ^ (2 : ℕ))) : ℝ) : ℂ) := by
  rw [suzukiTaV2BoundaryTorqueAnomaly,
    ← Complex.ofReal_sub, suzukiTaV2BoundaryCoefficient_sub_eq]
  push_cast
  have hs : Real.sinh a.1 ≠ 0 := (Real.sinh_pos_iff.mpr a.property).ne'
  have hc : Real.cosh a.1 ≠ 0 := (Real.cosh_pos a.1).ne'
  have hsum := suzukiTaV2ActualEnergy_add_ne_zero a
  field_simp [hs, hc, hsum]

theorem norm_suzukiTaV2BoundaryTorqueAnomaly_le
    (a : SuzukiPositiveAperture) :
    ‖suzukiTaV2BoundaryTorqueAnomaly a‖ ≤
      2 * a.1 / (Real.sinh a.1 * Real.cosh a.1) := by
  rw [suzukiTaV2BoundaryTorqueAnomaly_eq, norm_real, Real.norm_eq_abs,
    abs_neg]
  have he := suzukiTaV2ActualEvenEnergy_nonneg a
  have ho := suzukiTaV2ActualOddEnergy_nonneg a
  have hsum := suzukiTaV2ActualEnergy_add_pos a
  have hp : 0 < Real.sinh a.1 * Real.cosh a.1 :=
    mul_pos (Real.sinh_pos_iff.mpr a.property) (Real.cosh_pos a.1)
  have hden : 0 <
      (Real.sinh a.1 * Real.cosh a.1) *
        (suzukiTaV2ActualEvenEnergy a +
          suzukiTaV2ActualOddEnergy a) ^ (2 : ℕ) :=
    mul_pos hp (sq_pos_of_pos hsum)
  have hnum : 0 ≤
      8 * a.1 * suzukiTaV2ActualEvenEnergy a *
        suzukiTaV2ActualOddEnergy a :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) a.property.le) he) ho
  rw [abs_of_nonneg (div_nonneg hnum hden.le)]
  apply (div_le_div_iff₀ hden hp).2
  have hamgm :
      4 * suzukiTaV2ActualEvenEnergy a * suzukiTaV2ActualOddEnergy a ≤
        (suzukiTaV2ActualEvenEnergy a +
          suzukiTaV2ActualOddEnergy a) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg
      (suzukiTaV2ActualEvenEnergy a - suzukiTaV2ActualOddEnergy a)]
  have hscale : 0 ≤
      2 * a.1 * (Real.sinh a.1 * Real.cosh a.1) *
        ((suzukiTaV2ActualEvenEnergy a +
            suzukiTaV2ActualOddEnergy a) ^ (2 : ℕ) -
          4 * suzukiTaV2ActualEvenEnergy a *
            suzukiTaV2ActualOddEnergy a) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) a.property.le) hp.le)
      (sub_nonneg.mpr hamgm)
  nlinarith

theorem suzukiTaV2EndpointSecondTorque_boundarySourceLaw
    (a : SuzukiPositiveAperture) :
    (boundedPerturbedFormShift
        (suzukiWeilIntervalBoundedRemainder a) : ℂ) *
      (suzukiTaV2EndpointSecondTorque a -
        suzukiTaV2BoundaryTorqueAnomaly a) =
      suzukiTaV2ActualBoundarySourceTorque a := by
  have he := suzukiTaV2ActualEvenTilt_renormalized_sourceLaw a
  have ho := suzukiTaV2ActualOddTilt_renormalized_sourceLaw a
  rw [inner_cosh_covariance_cosh_eq_coalescingEvenEnergy] at he
  rw [inner_sinh_covariance_sinh_eq_coalescingOddEnergy] at ho
  have hecorr :
      (‖suzukiTaRawDeficiency a 1‖ : ℂ) *
          (suzukiTaV2EvenBoundaryCoefficient a : ℂ) *
          (suzukiTaCoalescingEvenEnergy a 1 : ℂ) =
        (suzukiTaV2EvenBoundaryCoefficient a : ℂ) *
          (suzukiTaV2ActualEvenEnergy a : ℂ) := by
    rw [suzukiTaV2ActualEvenEnergy]
    push_cast
    ring
  have hocorr :
      (‖suzukiTaRawDeficiency a 1‖ : ℂ) *
          (suzukiTaV2OddBoundaryCoefficient a : ℂ) *
          (suzukiTaCoalescingOddEnergy a 1 : ℂ) =
        (suzukiTaV2OddBoundaryCoefficient a : ℂ) *
          (suzukiTaV2ActualOddEnergy a : ℂ) := by
    rw [suzukiTaV2ActualOddEnergy]
    push_cast
    ring
  rw [hecorr] at he
  rw [hocorr] at ho
  change
    (boundedPerturbedFormShift
        (suzukiWeilIntervalBoundedRemainder a) : ℂ) *
        (suzukiTaV2ActualEvenTilt a -
          (suzukiTaV2EvenBoundaryCoefficient a : ℂ) *
            (suzukiTaV2ActualEvenEnergy a : ℂ)) =
      (‖suzukiTaRawDeficiency a 1‖ : ℂ) *
        suzukiTaV2ActualEvenBoundarySource a at he
  change
    (boundedPerturbedFormShift
        (suzukiWeilIntervalBoundedRemainder a) : ℂ) *
        (suzukiTaV2ActualOddTilt a -
          (suzukiTaV2OddBoundaryCoefficient a : ℂ) *
            (suzukiTaV2ActualOddEnergy a : ℂ)) =
      (‖suzukiTaRawDeficiency a 1‖ : ℂ) *
        suzukiTaV2ActualOddBoundarySource a at ho
  rw [suzukiTaV2EndpointSecondTorque_eq_actualParityCurvature,
    suzukiTaV2BoundaryTorqueAnomaly, suzukiTaV2ActualBoundarySourceTorque]
  field_simp [suzukiTaV2ActualEnergy_add_ne_zero a]
  linear_combination
    (suzukiTaV2ActualOddEnergy a : ℂ) * he -
    (suzukiTaV2ActualEvenEnergy a : ℂ) * ho

def suzukiTaV2NormalizedActualBoundarySourceTorque
    (a : SuzukiPositiveAperture) : ℂ :=
  (boundedPerturbedFormShift
      (suzukiWeilIntervalBoundedRemainder a) : ℂ)⁻¹ *
    suzukiTaV2ActualBoundarySourceTorque a

theorem suzukiTaV2NormalizedActualBoundarySourceTorque_eq
    (a : SuzukiPositiveAperture) :
    suzukiTaV2NormalizedActualBoundarySourceTorque a =
      suzukiTaV2EndpointSecondTorque a -
        suzukiTaV2BoundaryTorqueAnomaly a := by
  rw [suzukiTaV2NormalizedActualBoundarySourceTorque,
    ← suzukiTaV2EndpointSecondTorque_boundarySourceLaw]
  have hs :
      (boundedPerturbedFormShift
          (suzukiWeilIntervalBoundedRemainder a) : ℂ) ≠ 0 := by
    exact_mod_cast
      (boundedPerturbedFormShift_pos
        (suzukiWeilIntervalBoundedRemainder a)).ne'
  field_simp

theorem norm_suzukiTaV2NormalizedActualBoundarySourceTorque_le
    (a : SuzukiPositiveAperture) :
    ‖suzukiTaV2NormalizedActualBoundarySourceTorque a‖ ≤
      2 + 2 * a.1 / (Real.sinh a.1 * Real.cosh a.1) := by
  rw [suzukiTaV2NormalizedActualBoundarySourceTorque_eq]
  exact (norm_sub_le _ _).trans
    (add_le_add (norm_suzukiTaV2EndpointSecondTorque_le_two a)
      (norm_suzukiTaV2BoundaryTorqueAnomaly_le a))

theorem two_mul_aperture_div_sinh_mul_cosh_le_two
    (a : SuzukiPositiveAperture) :
    2 * a.1 / (Real.sinh a.1 * Real.cosh a.1) ≤ 2 := by
  have hs : a.1 ≤ Real.sinh a.1 := Real.self_le_sinh_iff.mpr a.property.le
  have hc : 1 ≤ Real.cosh a.1 := Real.one_le_cosh a.1
  have hs0 : 0 ≤ Real.sinh a.1 := Real.sinh_nonneg_iff.mpr a.property.le
  have hprod : a.1 ≤ Real.sinh a.1 * Real.cosh a.1 :=
    hs.trans (le_mul_of_one_le_right hs0 hc)
  have hp : 0 < Real.sinh a.1 * Real.cosh a.1 :=
    mul_pos (Real.sinh_pos_iff.mpr a.property) (Real.cosh_pos a.1)
  apply (div_le_iff₀ hp).2
  nlinarith

theorem norm_suzukiTaV2NormalizedActualBoundarySourceTorque_le_four
    (a : SuzukiPositiveAperture) :
    ‖suzukiTaV2NormalizedActualBoundarySourceTorque a‖ ≤ 4 := by
  exact (norm_suzukiTaV2NormalizedActualBoundarySourceTorque_le a).trans
    (by linarith [two_mul_aperture_div_sinh_mul_cosh_le_two a])

theorem tendsto_suzukiTaV2BoundaryTorqueAnomalyBound_atTop :
    Tendsto
      (fun a : ℝ => 2 * a / (Real.sinh a * Real.cosh a))
      atTop (nhds 0) := by
  have hscale : Tendsto (fun a : ℝ => 2 * a) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num)).mpr tendsto_id
  have hbase : Tendsto
      (fun a : ℝ => (2 * a) / Real.sinh (2 * a)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      GaloisForLFunctions.HTGeometry.tendsto_freeDefectAngle_atTop.comp hscale
  have hconst : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have htwo := hconst.mul hbase
  convert htwo using 1 <;> try norm_num
  funext a
  rw [Real.sinh_two_mul]
  ring


end RHTower
