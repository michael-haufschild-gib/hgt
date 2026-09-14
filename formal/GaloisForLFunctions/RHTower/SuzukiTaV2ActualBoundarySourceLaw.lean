import GaloisForLFunctions.RHTower.SuzukiTaV2BoundaryRenormalizedFormLift
import GaloisForLFunctions.RHTower.SuzukiTaV2ActualParityTorque

/-!
# Actual Suzuki boundary source law

Actual covariance position tilts are transported to Connes--Consani's completed Weil form without
assuming global position invariance of the logarithmic form domain. Forced hyperbolic endpoint
counterterms land the two probes in that domain. The shifted covariance equation then gives exact,
division-free even and odd identities retaining source overlap, archimedean, polar, and prime terms
in one coupled form value.
-/

open Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

def suzukiWeilIntervalCovarianceDomain (a : SuzukiPositiveAperture)
    (y : SuzukiApertureIntervalL2 a.1) :
    (suzukiWeilFriedrichsOperator a).domain :=
  ⟨suzukiWeilIntervalCovariance a y, by
    change suzukiWeilIntervalCovariance a y ∈
      (closedDenseInverse (suzukiWeilIntervalCovariance a)).domain
    exact (closedDenseInverse_apply_C (suzukiWeilIntervalCovariance a)
      (suzukiWeilIntervalCovariance_injective a) y).1⟩

theorem suzukiWeilIntervalCovariance_shiftEquation (a : SuzukiPositiveAperture)
    (y : SuzukiApertureIntervalL2 a.1) :
    suzukiWeilFriedrichsOperator a (suzukiWeilIntervalCovarianceDomain a y) +
      (boundedPerturbedFormShift
          (suzukiWeilIntervalBoundedRemainder a) : ℂ) •
        suzukiWeilIntervalCovariance a y = y := by
  change boundedPerturbedFriedrichsOperator
      (suzukiWeilIntervalFormEmbedding a)
      (suzukiWeilIntervalBoundedRemainder a)
      (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)
      (suzukiWeilIntervalCovarianceDomain a y) + _ = _
  rw [boundedPerturbedFriedrichsOperator_apply]
  change closedDenseInverse (suzukiWeilIntervalCovariance a)
        ⟨suzukiWeilIntervalCovariance a y, _⟩ -
      (boundedPerturbedFormShift
          (suzukiWeilIntervalBoundedRemainder a) : ℂ) •
        suzukiWeilIntervalCovariance a y +
      (boundedPerturbedFormShift
          (suzukiWeilIntervalBoundedRemainder a) : ℂ) •
        suzukiWeilIntervalCovariance a y = _
  rw [(closedDenseInverse_apply_C (suzukiWeilIntervalCovariance a)
    (suzukiWeilIntervalCovariance_injective a) y).2]
  module

def suzukiTaV2ActualEvenResponseFormVector (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a :=
  boundedPerturbedFormRieszInv
    (suzukiWeilIntervalFormEmbedding a)
    (suzukiWeilIntervalBoundedRemainder a)
    (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)
    ((suzukiWeilIntervalFormEmbedding a).adjoint
      ((suzukiApertureCoordinate a.2.le).coshVecC 1))

def suzukiTaV2ActualOddResponseFormVector (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a :=
  boundedPerturbedFormRieszInv
    (suzukiWeilIntervalFormEmbedding a)
    (suzukiWeilIntervalBoundedRemainder a)
    (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)
    ((suzukiWeilIntervalFormEmbedding a).adjoint
      ((suzukiApertureCoordinate a.2.le).sinhVecC 1))

theorem suzukiWeilIntervalFormEmbedding_actualEvenResponse (a : SuzukiPositiveAperture) :
    suzukiWeilIntervalFormEmbedding a (suzukiTaV2ActualEvenResponseFormVector a) =
      suzukiWeilIntervalCovariance a
        ((suzukiApertureCoordinate a.2.le).coshVecC 1) := by
  rfl

theorem suzukiWeilIntervalFormEmbedding_actualOddResponse (a : SuzukiPositiveAperture) :
    suzukiWeilIntervalFormEmbedding a (suzukiTaV2ActualOddResponseFormVector a) =
      suzukiWeilIntervalCovariance a
        ((suzukiApertureCoordinate a.2.le).sinhVecC 1) := by
  rfl

theorem suzukiTaV2ActualEvenResponse_represents (a : SuzukiPositiveAperture) :
    inner ℂ
        (suzukiWeilFriedrichsOperator a
          (suzukiWeilIntervalCovarianceDomain a
            ((suzukiApertureCoordinate a.2.le).coshVecC 1)))
        (suzukiTaV2EvenBoundary a) =
      suzukiWeilIntervalForm a (suzukiTaV2ActualEvenResponseFormVector a)
        (suzukiTaV2EvenBoundaryFormVector a) := by
  simpa only [suzukiWeilIntervalCovarianceDomain, suzukiTaV2ActualEvenResponseFormVector,
    suzukiWeilIntervalCovariance,
    suzukiWeilIntervalFormEmbedding_evenBoundaryFormVector] using
      (suzukiWeilFriedrichsOperator_represents_form a
        ((suzukiApertureCoordinate a.2.le).coshVecC 1)
        (suzukiTaV2EvenBoundaryFormVector a)).2

theorem suzukiTaV2ActualOddResponse_represents (a : SuzukiPositiveAperture) :
    inner ℂ
        (suzukiWeilFriedrichsOperator a
          (suzukiWeilIntervalCovarianceDomain a
            ((suzukiApertureCoordinate a.2.le).sinhVecC 1)))
        (suzukiTaV2OddBoundary a) =
      suzukiWeilIntervalForm a (suzukiTaV2ActualOddResponseFormVector a)
        (suzukiTaV2OddBoundaryFormVector a) := by
  simpa only [suzukiWeilIntervalCovarianceDomain, suzukiTaV2ActualOddResponseFormVector,
    suzukiWeilIntervalCovariance,
    suzukiWeilIntervalFormEmbedding_oddBoundaryFormVector] using
      (suzukiWeilFriedrichsOperator_represents_form a
        ((suzukiApertureCoordinate a.2.le).sinhVecC 1)
        (suzukiTaV2OddBoundaryFormVector a)).2

theorem suzukiTaV2ActualEvenBoundary_sourceLaw (a : SuzukiPositiveAperture) :
    (boundedPerturbedFormShift
        (suzukiWeilIntervalBoundedRemainder a) : ℂ) *
      inner ℂ (suzukiTaV2EvenBoundary a)
        (suzukiWeilIntervalCovariance a
          ((suzukiApertureCoordinate a.2.le).coshVecC 1)) =
      inner ℂ (suzukiTaV2EvenBoundary a)
          ((suzukiApertureCoordinate a.2.le).coshVecC 1) -
        (starRingEnd ℂ)
          (suzukiWeilIntervalForm a (suzukiTaV2ActualEvenResponseFormVector a)
            (suzukiTaV2EvenBoundaryFormVector a)) := by
  have h := congrArg (fun z => inner ℂ (suzukiTaV2EvenBoundary a) z)
    (suzukiWeilIntervalCovariance_shiftEquation a
      ((suzukiApertureCoordinate a.2.le).coshVecC 1))
  rw [inner_add_right, inner_smul_right] at h
  rw [← inner_conj_symm (suzukiTaV2EvenBoundary a),
    suzukiTaV2ActualEvenResponse_represents] at h
  rw [eq_sub_iff_add_eq]
  simpa only [add_comm] using h

theorem suzukiTaV2ActualOddBoundary_sourceLaw (a : SuzukiPositiveAperture) :
    (boundedPerturbedFormShift
        (suzukiWeilIntervalBoundedRemainder a) : ℂ) *
      inner ℂ (suzukiTaV2OddBoundary a)
        (suzukiWeilIntervalCovariance a
          ((suzukiApertureCoordinate a.2.le).sinhVecC 1)) =
      inner ℂ (suzukiTaV2OddBoundary a)
          ((suzukiApertureCoordinate a.2.le).sinhVecC 1) -
        (starRingEnd ℂ)
          (suzukiWeilIntervalForm a (suzukiTaV2ActualOddResponseFormVector a)
            (suzukiTaV2OddBoundaryFormVector a)) := by
  have h := congrArg (fun z => inner ℂ (suzukiTaV2OddBoundary a) z)
    (suzukiWeilIntervalCovariance_shiftEquation a
      ((suzukiApertureCoordinate a.2.le).sinhVecC 1))
  rw [inner_add_right, inner_smul_right] at h
  rw [← inner_conj_symm (suzukiTaV2OddBoundary a),
    suzukiTaV2ActualOddResponse_represents] at h
  rw [eq_sub_iff_add_eq]
  simpa only [add_comm] using h

theorem suzukiTaV2ActualEvenRawTilt_sourceLaw (a : SuzukiPositiveAperture) :
    (boundedPerturbedFormShift
        (suzukiWeilIntervalBoundedRemainder a) : ℂ) *
      (inner ℂ
          (suzukiAperturePosition a
            ((suzukiApertureCoordinate a.2.le).sinhVecC 1))
          (suzukiWeilIntervalCovariance a
            ((suzukiApertureCoordinate a.2.le).coshVecC 1)) -
        (suzukiTaV2EvenBoundaryCoefficient a : ℂ) *
          inner ℂ ((suzukiApertureCoordinate a.2.le).coshVecC 1)
            (suzukiWeilIntervalCovariance a
              ((suzukiApertureCoordinate a.2.le).coshVecC 1))) =
      inner ℂ (suzukiTaV2EvenBoundary a)
          ((suzukiApertureCoordinate a.2.le).coshVecC 1) -
        (starRingEnd ℂ)
          (suzukiWeilIntervalForm a (suzukiTaV2ActualEvenResponseFormVector a)
            (suzukiTaV2EvenBoundaryFormVector a)) := by
  rw [← suzukiTaV2ActualEvenBoundary_sourceLaw]
  rw [suzukiTaV2EvenBoundary_eq_position, inner_sub_left,
    inner_smul_left]
  rw [Complex.conj_ofReal]

theorem suzukiTaV2ActualOddRawTilt_sourceLaw (a : SuzukiPositiveAperture) :
    (boundedPerturbedFormShift
        (suzukiWeilIntervalBoundedRemainder a) : ℂ) *
      (inner ℂ
          (suzukiAperturePosition a
            ((suzukiApertureCoordinate a.2.le).coshVecC 1))
          (suzukiWeilIntervalCovariance a
            ((suzukiApertureCoordinate a.2.le).sinhVecC 1)) -
        (suzukiTaV2OddBoundaryCoefficient a : ℂ) *
          inner ℂ ((suzukiApertureCoordinate a.2.le).sinhVecC 1)
            (suzukiWeilIntervalCovariance a
              ((suzukiApertureCoordinate a.2.le).sinhVecC 1))) =
      inner ℂ (suzukiTaV2OddBoundary a)
          ((suzukiApertureCoordinate a.2.le).sinhVecC 1) -
        (starRingEnd ℂ)
          (suzukiWeilIntervalForm a (suzukiTaV2ActualOddResponseFormVector a)
            (suzukiTaV2OddBoundaryFormVector a)) := by
  rw [← suzukiTaV2ActualOddBoundary_sourceLaw]
  rw [suzukiTaV2OddBoundary_eq_position, inner_sub_left,
    inner_smul_left]
  rw [Complex.conj_ofReal]

/-- Division-free source law for the normalized actual even endpoint tilt. -/
theorem suzukiTaV2ActualEvenTilt_renormalized_sourceLaw
    (a : SuzukiPositiveAperture) :
    (boundedPerturbedFormShift
        (suzukiWeilIntervalBoundedRemainder a) : ℂ) *
      (suzukiTaV2ActualEvenTilt a -
        (‖suzukiTaRawDeficiency a 1‖ : ℂ) *
          (suzukiTaV2EvenBoundaryCoefficient a : ℂ) *
          inner ℂ ((suzukiApertureCoordinate a.2.le).coshVecC 1)
            (suzukiWeilIntervalCovariance a
              ((suzukiApertureCoordinate a.2.le).coshVecC 1))) =
      (‖suzukiTaRawDeficiency a 1‖ : ℂ) *
        (inner ℂ (suzukiTaV2EvenBoundary a)
            ((suzukiApertureCoordinate a.2.le).coshVecC 1) -
          (starRingEnd ℂ)
            (ccmRestrictedWeilForm a
              (suzukiTaV2ActualEvenResponseFormVector a)
              (suzukiTaV2EvenBoundaryFormVector a))) := by
  rw [suzukiTaV2ActualEvenTilt, ← suzukiWeilIntervalForm_eq_ccmRestrictedWeilForm,
    ← suzukiTaV2ActualEvenRawTilt_sourceLaw]
  ring

/-- Division-free source law for the normalized actual odd endpoint tilt. -/
theorem suzukiTaV2ActualOddTilt_renormalized_sourceLaw
    (a : SuzukiPositiveAperture) :
    (boundedPerturbedFormShift
        (suzukiWeilIntervalBoundedRemainder a) : ℂ) *
      (suzukiTaV2ActualOddTilt a -
        (‖suzukiTaRawDeficiency a 1‖ : ℂ) *
          (suzukiTaV2OddBoundaryCoefficient a : ℂ) *
          inner ℂ ((suzukiApertureCoordinate a.2.le).sinhVecC 1)
            (suzukiWeilIntervalCovariance a
              ((suzukiApertureCoordinate a.2.le).sinhVecC 1))) =
      (‖suzukiTaRawDeficiency a 1‖ : ℂ) *
        (inner ℂ (suzukiTaV2OddBoundary a)
            ((suzukiApertureCoordinate a.2.le).sinhVecC 1) -
          (starRingEnd ℂ)
            (ccmRestrictedWeilForm a
              (suzukiTaV2ActualOddResponseFormVector a)
              (suzukiTaV2OddBoundaryFormVector a))) := by
  rw [suzukiTaV2ActualOddTilt, ← suzukiWeilIntervalForm_eq_ccmRestrictedWeilForm,
    ← suzukiTaV2ActualOddRawTilt_sourceLaw]
  ring

end RHTower
