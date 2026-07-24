import GaloisForLFunctions.RHTower.LocalDivisorJetRelativeKOne
import GaloisForLFunctions.RHTower.XiCompletedAperturePoleResonance
import GaloisForLFunctions.RHTower.XiHedenmalmSimplicityUniversalityLaw

/-!
# Xi aperture-collision relative-K1 simplicity tomography

The filled resonant two-point aperture determinant is the scalar multiplicity tomograph
`-4m²`. Its distinguished value `-4` therefore detects precisely the simple-zero phase, which is
also local Hedenmalm normality, triviality of the canonical relative unit, and vanishing of the
finite logarithmic regulator.
-/

namespace RHTower

noncomputable section

/-- Uniform simple-zero value of the filled resonant aperture determinant. -/
def XiApertureSimpleCollisionCertificate : Prop :=
  ∀ rho : XiDivisorSupport,
    xiCompletedApertureRegularizedResonantTwoPointDet rho 0 = -4

/-- The filled aperture collision has value `-4` exactly at multiplicity one. -/
theorem xiCompletedApertureRegularizedResonantTwoPointDet_eq_neg_four_iff
    (rho : XiDivisorSupport) :
    xiCompletedApertureRegularizedResonantTwoPointDet rho 0 = -4 ↔
      xiSupportMultiplicity rho = 1 := by
  rw [xiCompletedApertureRegularizedResonantTwoPointDet_zero]
  constructor
  · intro h
    have hmpos : 0 < (xiSupportMultiplicity rho : ℝ) := by
      exact_mod_cast xiSupportMultiplicity_pos rho
    have hmreal : (xiSupportMultiplicity rho : ℝ) = 1 := by
      nlinarith
    exact_mod_cast hmreal
  · rintro h
    rw [h]
    norm_num

/-- **Pointwise aperture/Jordan/relative-K1 tomography.** Collision value `-4`, local Jordan
normality, triviality of the canonical relative unit, and regulator vanishing are one phase. -/
theorem xiCompletedApertureCollision_neg_four_iff_completeLocalSimplicity
    (rho : XiDivisorSupport) :
    xiCompletedApertureRegularizedResonantTwoPointDet rho 0 = -4 ↔
      XiLocalJordanNormal rho ∧
      localDivisorJetInfinitesimalUnit ℂ (xiSupportMultiplicity rho) = 1 ∧
      localDivisorJetLogUnit (xiSupportMultiplicity rho) = 0 := by
  rw [xiCompletedApertureRegularizedResonantTwoPointDet_eq_neg_four_iff rho,
    xiLocalJordanNormal_iff_multiplicity_one]
  rw [localDivisorJetInfinitesimalUnit_eq_one_iff ℂ
    (xiSupportMultiplicity_pos rho)]
  rw [localDivisorJetLogUnit_eq_zero_iff (xiSupportMultiplicity_pos rho)]
  simp

/-- Global Xi simplicity is exactly uniform filled-aperture collision value `-4`. -/
theorem xiZerosSimple_iff_apertureSimpleCollisionCertificate :
    XiZerosSimple ↔ XiApertureSimpleCollisionCertificate := by
  rw [← all_xiLocalJordanNormal_iff_simple]
  constructor
  · intro hnormal rho
    exact (xiCompletedApertureRegularizedResonantTwoPointDet_eq_neg_four_iff rho).2
      ((xiLocalJordanNormal_iff_multiplicity_one rho).1 (hnormal rho))
  · intro hcollision rho
    exact (xiLocalJordanNormal_iff_multiplicity_one rho).2
      ((xiCompletedApertureRegularizedResonantTwoPointDet_eq_neg_four_iff rho).1
        (hcollision rho))

/-- **Xi aperture-collision relative-K1 simplicity-tomography universality law.** Uniform scalar
collision value `-4`, global Xi simplicity, and the complete eight-chart Hedenmalm certificate are
equivalent; pointwise the same scalar also detects the relative-`K₁` and regulator phase. -/
theorem xiApertureCollision_completeRelativeKOneSimplicityTomographyUniversality :
    (XiZerosSimple ↔ XiApertureSimpleCollisionCertificate) ∧
    (XiHedenmalmSimplicityUniversalCertificate ↔
      XiApertureSimpleCollisionCertificate) := by
  refine ⟨xiZerosSimple_iff_apertureSimpleCollisionCertificate, ?_⟩
  exact
    xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate.symm.trans
      xiZerosSimple_iff_apertureSimpleCollisionCertificate

end

end RHTower
