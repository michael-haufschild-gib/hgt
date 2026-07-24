import GaloisForLFunctions.RHTower.SoninCoupledPositiveApertureUniversalityLaw
import GaloisForLFunctions.RHTower.XiHedenmalmSimplicityUniversalityLaw

/-!
# Xi positive-Sonin Hedenmalm simplicity universality

The determinant collar at every plain positive Sonin aperture detects exactly RH, while the
Hedenmalm simplicity certificate detects exactly simple Xi zeros.  Combining these intrinsic
classifications removes the proof-carrying source-nondegeneracy artifact from the complete
RH-and-simplicity interface, pointwise and simultaneously over the positive aperture family.
-/

namespace RHTower

noncomputable section

/-- RH is exactly simultaneous relative-determinant collar control over every plain positive
Sonin aperture. -/
theorem riemannHypothesis_iff_allSoninPositiveApertureUnitCollarPhase :
    RiemannHypothesis ↔ SoninAllPositiveApertureUnitCollarPhase :=
  primeArchSourceMomentHankelExactReconstructionPhase_iff_riemannHypothesis.symm.trans
    primeArchSourceMomentHankelExactReconstructionPhase_iff_allSoninPositiveApertureUnitCollarPhase

/-- Non-RH is exactly synchronized collar failure over every plain positive Sonin aperture. -/
theorem not_riemannHypothesis_iff_allSoninPositiveApertureUnitCollarFailurePhase :
    ¬RiemannHypothesis ↔ SoninAllPositiveApertureUnitCollarFailurePhase :=
  (not_congr
    primeArchSourceMomentHankelExactReconstructionPhase_iff_riemannHypothesis).symm.trans
      not_primeArchSourceMomentHankelExactReconstructionPhase_iff_allSoninPositiveApertureUnitCollarFailurePhase

/-- **Positive-Sonin/Hedenmalm universality law.** At any plain positive aperture, its concrete
relative determinant collar together with simple Xi zeros is exactly the full Hedenmalm
RH-and-simplicity certificate. -/
theorem
    soninPositiveApertureRelativeDeterminant_unitCollar_and_xiZerosSimple_iff_hendenmalmUniversalCertificate
    (a : SoninPositiveAperture) :
    (UnitCollarExponentialEnvelope (fun n =>
          bernsteinCoefficientPurity
            (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment
              (soninCoupledNondegenerateAperture a)) n) ∧
        XiZerosSimple) ↔
      XiHedenmalmRHSimplicityUniversalCertificate :=
  (and_congr
    (riemannHypothesis_iff_soninPositiveApertureRelativeDeterminant_unitCollar a).symm
    Iff.rfl).trans
      riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate

/-- Certificate-only pointwise form: one positive-aperture determinant collar and the eight-chart
Hedenmalm simplicity phase are exactly the enlarged RH-and-simplicity certificate. -/
theorem
    soninPositiveApertureRelativeDeterminant_unitCollar_and_hendenmalmSimplicity_iff_rhSimplicityCertificate
    (a : SoninPositiveAperture) :
    (UnitCollarExponentialEnvelope (fun n =>
          bernsteinCoefficientPurity
            (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment
              (soninCoupledNondegenerateAperture a)) n) ∧
        XiHedenmalmSimplicityUniversalCertificate) ↔
      XiHedenmalmRHSimplicityUniversalCertificate :=
  (and_congr Iff.rfl
    xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate.symm).trans
      (soninPositiveApertureRelativeDeterminant_unitCollar_and_xiZerosSimple_iff_hendenmalmUniversalCertificate
        a)

/-- Simultaneous collars over all positive apertures together with simple Xi zeros are exactly the
full Hedenmalm RH-and-simplicity certificate. -/
theorem
    allSoninPositiveApertureUnitCollarPhase_and_xiZerosSimple_iff_hendenmalmUniversalCertificate :
    (SoninAllPositiveApertureUnitCollarPhase ∧ XiZerosSimple) ↔
      XiHedenmalmRHSimplicityUniversalCertificate :=
  (and_congr
    riemannHypothesis_iff_allSoninPositiveApertureUnitCollarPhase.symm
    Iff.rfl).trans
      riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate

/-- Certificate-only simultaneous form over the whole intrinsic positive-aperture domain. -/
theorem
    allSoninPositiveApertureUnitCollarPhase_and_hendenmalmSimplicity_iff_rhSimplicityCertificate :
    (SoninAllPositiveApertureUnitCollarPhase ∧
        XiHedenmalmSimplicityUniversalCertificate) ↔
      XiHedenmalmRHSimplicityUniversalCertificate :=
  (and_congr Iff.rfl
    xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate.symm).trans
      allSoninPositiveApertureUnitCollarPhase_and_xiZerosSimple_iff_hendenmalmUniversalCertificate

/-- Pointwise failure law: the enlarged Hedenmalm certificate fails exactly when the chosen
positive-aperture collar fails or Xi has a multiple zero. -/
theorem
    not_soninPositiveApertureRelativeDeterminant_unitCollar_or_not_xiZerosSimple_iff_not_hendenmalmUniversalCertificate
    (a : SoninPositiveAperture) :
    (¬UnitCollarExponentialEnvelope (fun n =>
          bernsteinCoefficientPurity
            (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment
              (soninCoupledNondegenerateAperture a)) n) ∨
        ¬XiZerosSimple) ↔
      ¬XiHedenmalmRHSimplicityUniversalCertificate := by
  constructor
  · intro hfailure hcertificate
    have hphase :=
      (soninPositiveApertureRelativeDeterminant_unitCollar_and_xiZerosSimple_iff_hendenmalmUniversalCertificate
        a).2 hcertificate
    exact hfailure.elim (fun h => h hphase.1) (fun h => h hphase.2)
  · intro hnotCertificate
    by_cases hcollar : UnitCollarExponentialEnvelope (fun n =>
        bernsteinCoefficientPurity
          (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment
            (soninCoupledNondegenerateAperture a)) n)
    · right
      intro hsimple
      exact hnotCertificate
        ((soninPositiveApertureRelativeDeterminant_unitCollar_and_xiZerosSimple_iff_hendenmalmUniversalCertificate
          a).1 ⟨hcollar, hsimple⟩)
    · exact Or.inl hcollar

/-- Certificate-only pointwise failure law. -/
theorem
    not_soninPositiveApertureRelativeDeterminant_unitCollar_or_not_hendenmalmSimplicity_iff_not_rhSimplicityCertificate
    (a : SoninPositiveAperture) :
    (¬UnitCollarExponentialEnvelope (fun n =>
          bernsteinCoefficientPurity
            (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment
              (soninCoupledNondegenerateAperture a)) n) ∨
        ¬XiHedenmalmSimplicityUniversalCertificate) ↔
      ¬XiHedenmalmRHSimplicityUniversalCertificate :=
  (or_congr Iff.rfl
    (not_congr xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate).symm).trans
      (not_soninPositiveApertureRelativeDeterminant_unitCollar_or_not_xiZerosSimple_iff_not_hendenmalmUniversalCertificate
        a)

/-- Synchronized failure law: the enlarged certificate fails exactly when collars fail at every
positive aperture or Xi has a multiple zero. -/
theorem
    allSoninPositiveApertureUnitCollarFailurePhase_or_not_xiZerosSimple_iff_not_hendenmalmUniversalCertificate :
    (SoninAllPositiveApertureUnitCollarFailurePhase ∨ ¬XiZerosSimple) ↔
      ¬XiHedenmalmRHSimplicityUniversalCertificate := by
  constructor
  · intro hfailure hcertificate
    have hphase :=
      riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate.2
        hcertificate
    exact hfailure.elim
      (fun h => (not_riemannHypothesis_iff_allSoninPositiveApertureUnitCollarFailurePhase.2 h)
        hphase.1)
      (fun h => h hphase.2)
  · intro hnotCertificate
    by_cases hsimple : XiZerosSimple
    · left
      apply not_riemannHypothesis_iff_allSoninPositiveApertureUnitCollarFailurePhase.1
      intro hRH
      exact hnotCertificate
        (riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate.1
          ⟨hRH, hsimple⟩)
    · exact Or.inr hsimple

/-- Certificate-only synchronized failure law over all positive apertures. -/
theorem
    allSoninPositiveApertureUnitCollarFailurePhase_or_not_hendenmalmSimplicity_iff_not_rhSimplicityCertificate :
    (SoninAllPositiveApertureUnitCollarFailurePhase ∨
        ¬XiHedenmalmSimplicityUniversalCertificate) ↔
      ¬XiHedenmalmRHSimplicityUniversalCertificate :=
  (or_congr Iff.rfl
    (not_congr xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate).symm).trans
      allSoninPositiveApertureUnitCollarFailurePhase_or_not_xiZerosSimple_iff_not_hendenmalmUniversalCertificate

end

end RHTower
