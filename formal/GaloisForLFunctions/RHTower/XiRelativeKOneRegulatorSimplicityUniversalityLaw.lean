import GaloisForLFunctions.RHTower.LocalDivisorJetRelativeKOne
import GaloisForLFunctions.RHTower.XiHedenmalmSimplicityUniversalityLaw

/-!
# Xi relative-K1 regulator simplicity universality

The local Xi multiplicity has three exact and apparently different classifiers: normality of its
Hedenmalm Jordan block, triviality of the canonical relative unit in the local divisor algebra,
and vanishing of that unit's truncated logarithmic regulator. Pointwise they are the same
multiplicity-one phase. Globally the relative-algebraic conditions are therefore equivalent to Xi
simplicity and to the complete existing Hedenmalm simplicity certificate.
-/

namespace RHTower

noncomputable section

/-- Simultaneous relative-`K₁` and logarithmic-regulator simplicity at every Xi divisor point. -/
def XiRelativeKOneRegulatorSimplicityCertificate : Prop :=
  (∀ rho : XiDivisorSupport,
    localDivisorJetInfinitesimalUnit ℂ (xiSupportMultiplicity rho) = 1) ∧
  ∀ rho : XiDivisorSupport,
    localDivisorJetLogUnit (xiSupportMultiplicity rho) = 0

/-- **Pointwise relative-K1/Jordan/regulator universality.** A local Xi Hedenmalm block is normal
exactly when the canonical relative unit of its divisor jet is trivial and its finite logarithmic
regulator vanishes. All three conditions classify multiplicity one. -/
theorem xiLocalJordanNormal_iff_relativeKOneTrivial_and_logRegulatorVanishing
    (rho : XiDivisorSupport) :
    XiLocalJordanNormal rho ↔
      localDivisorJetInfinitesimalUnit ℂ (xiSupportMultiplicity rho) = 1 ∧
      localDivisorJetLogUnit (xiSupportMultiplicity rho) = 0 := by
  rw [xiLocalJordanNormal_iff_multiplicity_one]
  rw [localDivisorJetInfinitesimalUnit_eq_one_iff ℂ
    (xiSupportMultiplicity_pos rho)]
  rw [localDivisorJetLogUnit_eq_zero_iff (xiSupportMultiplicity_pos rho)]
  simp

/-- Global Xi simplicity is exactly simultaneous triviality of the canonical relative-`K₁` unit
and vanishing of its logarithmic regulator at every divisor support point. -/
theorem xiZerosSimple_iff_relativeKOneRegulatorSimplicityCertificate :
    XiZerosSimple ↔ XiRelativeKOneRegulatorSimplicityCertificate := by
  rw [← all_xiLocalJordanNormal_iff_simple]
  constructor
  · intro hall
    exact ⟨
      fun rho =>
        (xiLocalJordanNormal_iff_relativeKOneTrivial_and_logRegulatorVanishing rho).1
          (hall rho) |>.1,
      fun rho =>
        (xiLocalJordanNormal_iff_relativeKOneTrivial_and_logRegulatorVanishing rho).1
          (hall rho) |>.2⟩
  · intro h rho
    exact
      (xiLocalJordanNormal_iff_relativeKOneTrivial_and_logRegulatorVanishing rho).2
        ⟨h.1 rho, h.2 rho⟩

/-- **Xi relative-K1 regulator simplicity universality law.** The relative local-divisor
certificate, global Xi simplicity, and the complete eight-chart Hedenmalm certificate are one
phase. This adds unconditional relative algebraic-`K₁` and regulator charts to the existing
analytic, Hilbert, Jordan, Bezoutian, continuation, and theta-source classification. -/
theorem xiSimplicity_completeRelativeKOneRegulatorUniversality :
    (XiZerosSimple ↔ XiRelativeKOneRegulatorSimplicityCertificate) ∧
    (XiHedenmalmSimplicityUniversalCertificate ↔
      XiRelativeKOneRegulatorSimplicityCertificate) := by
  refine ⟨xiZerosSimple_iff_relativeKOneRegulatorSimplicityCertificate, ?_⟩
  exact
    xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate.symm.trans
      xiZerosSimple_iff_relativeKOneRegulatorSimplicityCertificate

end

end RHTower
