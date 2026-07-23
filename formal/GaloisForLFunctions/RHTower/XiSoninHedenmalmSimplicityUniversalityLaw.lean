import GaloisForLFunctions.RHTower.SoninCoupledRelativeDeterminantRHUniversalityLaw
import GaloisForLFunctions.RHTower.XiHedenmalmSimplicityUniversalityLaw

/-!
# Xi Sonin--Hedenmalm simplicity universality

The relative determinant collar at any one nondegenerate coupled-Sonin aperture detects exactly
RH.  The Hedenmalm simplicity certificate detects exactly simple Xi zeros.  Combining those
existing classifications identifies one concrete Fredholm-determinant aperture and the terminal
Hilbert/continuation/Jordan simplicity package with the full RH-and-simplicity phase.
-/

namespace RHTower

noncomputable section

/-- **Single-Sonin/Hedenmalm universality law.** At any nondegenerate coupled-Sonin aperture, its
relative determinant collar together with simple Xi zeros is exactly the full Hedenmalm
RH-and-simplicity certificate. -/
theorem
    soninCoupledRelativeDeterminant_unitCollar_and_xiZerosSimple_iff_hendenmalmUniversalCertificate
    (a : SoninCoupledNondegenerateAperture) :
    (UnitCollarExponentialEnvelope (fun n =>
          bernsteinCoefficientPurity
            (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n) ∧
        XiZerosSimple) ↔
      XiHedenmalmRHSimplicityUniversalCertificate :=
  (and_congr
    (riemannHypothesis_iff_soninCoupledRelativeDeterminant_unitCollar a).symm
    Iff.rfl).trans
      riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate

/-- Certificate-only positive form: one Sonin determinant collar and the eight-chart Hedenmalm
simplicity phase are exactly the enlarged RH-and-simplicity certificate. -/
theorem
    soninCoupledRelativeDeterminant_unitCollar_and_hendenmalmSimplicity_iff_rhSimplicityCertificate
    (a : SoninCoupledNondegenerateAperture) :
    (UnitCollarExponentialEnvelope (fun n =>
          bernsteinCoefficientPurity
            (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n) ∧
        XiHedenmalmSimplicityUniversalCertificate) ↔
      XiHedenmalmRHSimplicityUniversalCertificate :=
  (and_congr Iff.rfl
    xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate.symm).trans
      (soninCoupledRelativeDeterminant_unitCollar_and_xiZerosSimple_iff_hendenmalmUniversalCertificate
        a)

/-- **Single-Sonin/Hedenmalm failure classification.** Failure of the enlarged certificate is
exactly failure of the chosen determinant collar or failure of Xi simplicity. -/
theorem
    not_soninCoupledRelativeDeterminant_unitCollar_or_not_xiZerosSimple_iff_not_hendenmalmUniversalCertificate
    (a : SoninCoupledNondegenerateAperture) :
    (¬UnitCollarExponentialEnvelope (fun n =>
          bernsteinCoefficientPurity
            (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n) ∨
        ¬XiZerosSimple) ↔
      ¬XiHedenmalmRHSimplicityUniversalCertificate := by
  constructor
  · intro hfailure hcertificate
    have hphase :=
      riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate.2
        hcertificate
    rcases hfailure with hnotCollar | hnotSimple
    · exact hnotCollar
        (riemannHypothesis_iff_soninCoupledRelativeDeterminant_unitCollar a |>.1 hphase.1)
    · exact hnotSimple hphase.2
  · intro hnotCertificate
    by_cases hcollar : UnitCollarExponentialEnvelope (fun n =>
        bernsteinCoefficientPurity
          (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n)
    · right
      intro hsimple
      exact hnotCertificate
        (soninCoupledRelativeDeterminant_unitCollar_and_xiZerosSimple_iff_hendenmalmUniversalCertificate
          a |>.1 ⟨hcollar, hsimple⟩)
    · exact Or.inl hcollar

/-- Certificate-only negative form: failure of the enlarged Hedenmalm certificate is exactly
failure of the chosen Sonin collar or failure of the eight-chart simplicity certificate. -/
theorem
    not_soninCoupledRelativeDeterminant_unitCollar_or_not_hendenmalmSimplicity_iff_not_rhSimplicityCertificate
    (a : SoninCoupledNondegenerateAperture) :
    (¬UnitCollarExponentialEnvelope (fun n =>
          bernsteinCoefficientPurity
            (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n) ∨
        ¬XiHedenmalmSimplicityUniversalCertificate) ↔
      ¬XiHedenmalmRHSimplicityUniversalCertificate :=
  (or_congr Iff.rfl
    (not_congr xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate).symm).trans
      (not_soninCoupledRelativeDeterminant_unitCollar_or_not_xiZerosSimple_iff_not_hendenmalmUniversalCertificate
        a)

end

end RHTower
