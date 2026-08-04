import GaloisForLFunctions.HTGeometry.ClockPropagatorSelfCalibration

/-!
# Two masses calibrate the backreaction-subtracted contrast

Switching the target-probe coupling off and on and subtracting the measured inverse probe responses
leaves the hidden Green element of the clock field, dressed on both sides by the unknown endpoint
gains and coupling maps. That contrast is inverted by the endpoint-dressed mass-shifted operator of
the species.

Repeating the experiment with a second calibrated squared mass therefore cancels the hidden
geometric operator entirely: the difference of the two inverted contrasts is the mass difference
times the endpoint-calibration product, and division by the mass difference reconstructs that
product.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

section TwoMassContrast

variable {K : Type u} {A : Type v} [Field K] [Ring A] [Algebra K A]

/-- The measured inverse of a species is the endpoint-dressed mass-shifted operator. -/
theorem measuredClockInverse_eq_endpointDressedInverse
    (geometricOperator sourceGainInv receiverGainInv : A) (massSq : K) :
    measuredClockInverse geometricOperator sourceGainInv receiverGainInv massSq =
      endpointDressedInverse sourceGainInv (geometricOperator + algebraMap K A massSq)
        receiverGainInv := rfl

/-- **The backreaction-subtracted contrast of a species is inverted by its measured clock
inverse.** -/
theorem measuredClockInverse_isTwoSided_backreactionSubtracted
    (probeOperator probeSourceGainInv receiverCoupling targetGreen sourceCoupling
      probeReceiverGainInv geometricOperator leftDressingInv rightDressingInv : A)
    (massSq : K)
    (hTargetOperatorGreen : (geometricOperator + algebraMap K A massSq) * targetGreen = 1)
    (hTargetGreenOperator : targetGreen * (geometricOperator + algebraMap K A massSq) = 1)
    (hLeftInv : leftDressingInv * (probeSourceGainInv * receiverCoupling) = 1)
    (hLeft : (probeSourceGainInv * receiverCoupling) * leftDressingInv = 1)
    (hRightInv : rightDressingInv * (sourceCoupling * probeReceiverGainInv) = 1)
    (hRight : (sourceCoupling * probeReceiverGainInv) * rightDressingInv = 1) :
    measuredClockInverse geometricOperator rightDressingInv leftDressingInv massSq *
          backreactionSubtractedHiddenGreen probeOperator probeSourceGainInv receiverCoupling
            targetGreen sourceCoupling probeReceiverGainInv = 1 ∧
      backreactionSubtractedHiddenGreen probeOperator probeSourceGainInv receiverCoupling
            targetGreen sourceCoupling probeReceiverGainInv *
          measuredClockInverse geometricOperator rightDressingInv leftDressingInv massSq = 1 :=
  backreactionSubtractedHiddenGreen_inverse_isTwoSided probeOperator probeSourceGainInv
    receiverCoupling targetGreen sourceCoupling probeReceiverGainInv
    (geometricOperator + algebraMap K A massSq) leftDressingInv rightDressingInv
    hTargetOperatorGreen hTargetGreenOperator hLeftInv hLeft hRightInv hRight

/-- **Two masses calibrate the backreaction-subtracted contrast.**

Each species' coupling-off/coupling-on contrast is inverted by its measured clock inverse; the
difference of those inverses cancels the hidden geometric operator, and division by the calibrated
mass difference reconstructs the endpoint-calibration product exactly. No weak-coupling expansion
and no absolute gain calibration are used. -/
theorem backreactionSubtracted_twoMass_calibration
    (probeOperator probeSourceGainInv receiverCoupling sourceCoupling probeReceiverGainInv
      geometricOperator leftDressingInv rightDressingInv targetGreen₁ targetGreen₂ : A)
    {massSq₁ massSq₂ : K} (hmass : massSq₁ ≠ massSq₂)
    (hTargetOperatorGreen₁ : (geometricOperator + algebraMap K A massSq₁) * targetGreen₁ = 1)
    (hTargetGreenOperator₁ : targetGreen₁ * (geometricOperator + algebraMap K A massSq₁) = 1)
    (hTargetOperatorGreen₂ : (geometricOperator + algebraMap K A massSq₂) * targetGreen₂ = 1)
    (hTargetGreenOperator₂ : targetGreen₂ * (geometricOperator + algebraMap K A massSq₂) = 1)
    (hLeftInv : leftDressingInv * (probeSourceGainInv * receiverCoupling) = 1)
    (hLeft : (probeSourceGainInv * receiverCoupling) * leftDressingInv = 1)
    (hRightInv : rightDressingInv * (sourceCoupling * probeReceiverGainInv) = 1)
    (hRight : (sourceCoupling * probeReceiverGainInv) * rightDressingInv = 1) :
    (measuredClockInverse geometricOperator rightDressingInv leftDressingInv massSq₁ *
          backreactionSubtractedHiddenGreen probeOperator probeSourceGainInv receiverCoupling
            targetGreen₁ sourceCoupling probeReceiverGainInv = 1 ∧
        backreactionSubtractedHiddenGreen probeOperator probeSourceGainInv receiverCoupling
              targetGreen₁ sourceCoupling probeReceiverGainInv *
            measuredClockInverse geometricOperator rightDressingInv leftDressingInv massSq₁ = 1) ∧
      (measuredClockInverse geometricOperator rightDressingInv leftDressingInv massSq₂ *
            backreactionSubtractedHiddenGreen probeOperator probeSourceGainInv receiverCoupling
              targetGreen₂ sourceCoupling probeReceiverGainInv = 1 ∧
          backreactionSubtractedHiddenGreen probeOperator probeSourceGainInv receiverCoupling
                targetGreen₂ sourceCoupling probeReceiverGainInv *
              measuredClockInverse geometricOperator rightDressingInv leftDressingInv massSq₂
            = 1) ∧
        algebraMap K A (massSq₁ - massSq₂)⁻¹ *
            (measuredClockInverse geometricOperator rightDressingInv leftDressingInv massSq₁ -
              measuredClockInverse geometricOperator rightDressingInv leftDressingInv massSq₂) =
          rightDressingInv * leftDressingInv := by
  refine ⟨measuredClockInverse_isTwoSided_backreactionSubtracted probeOperator probeSourceGainInv
      receiverCoupling targetGreen₁ sourceCoupling probeReceiverGainInv geometricOperator
      leftDressingInv rightDressingInv massSq₁ hTargetOperatorGreen₁ hTargetGreenOperator₁
      hLeftInv hLeft hRightInv hRight,
    measuredClockInverse_isTwoSided_backreactionSubtracted probeOperator probeSourceGainInv
      receiverCoupling targetGreen₂ sourceCoupling probeReceiverGainInv geometricOperator
      leftDressingInv rightDressingInv massSq₂ hTargetOperatorGreen₂ hTargetGreenOperator₂
      hLeftInv hLeft hRightInv hRight, ?_⟩
  exact endpointCalibrationProduct_reconstruction geometricOperator rightDressingInv
    leftDressingInv hmass

end TwoMassContrast

end GaloisForLFunctions.HTGeometry
