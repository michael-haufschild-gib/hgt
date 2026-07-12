import GaloisForLFunctions.RHTower.XiHedenmalmSourceCapstone
import GaloisForLFunctions.RHTower.XiHedenmalmMultiplicityChain

/-!
# Hedenmalm completeness as a static value constraint

The Hedenmalm eigenfamily's density condition is a Hilbert-space closure
statement, but the multiplicity chain shows that its exact content is local:
the first removable quotient must be nonzero at every Xi divisor point.  This
file replaces the completion interface by that pointwise value law.

Combining it with the continued prime--Gamma one-Cauchy value inequality gives
a formulation of `RH + simplicity` entirely in terms of static source and
quotient values.  No limiting span, evolution, or operator construction occurs
in the theorem statement.
-/

namespace RHTower

noncomputable section

/-- The first Hedenmalm removable quotient is nonzero at every Xi divisor point. -/
def XiThetaFirstQuotientValueConstraint : Prop :=
  ∀ rho : XiDivisorSupport,
    xiThetaEigenFourier (xiSpectralPointSupport rho)
      (xiSpectralPointSupport rho) ≠ 0

/-- The local quotient-value constraint is exactly simplicity of every Xi zero. -/
theorem xiThetaFirstQuotientValueConstraint_iff_simple :
    XiThetaFirstQuotientValueConstraint ↔ XiZerosSimple := by
  constructor
  · intro h alpha halpha
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy alpha).mp halpha
    have hvalue := h q.1
    have hvalue' : xiThetaEigenFourier alpha alpha ≠ 0 := by
      simpa only [← hq, xiSpectralPoint_eq_support] using hvalue
    rw [xiThetaEigenFourier_self] at hvalue'
    exact fun hderiv => hvalue' (by rw [hderiv, mul_zero])
  · intro hsimple rho
    apply (xiThetaEigenFourier_self_ne_zero_iff_multiplicity_one rho).2
    exact xiDivisorMultiplicity_eq_one_of_simple hsimple rho

/-- Fully exposed static-value formulation of `RH + simplicity`: one continued prime--Gamma
divided-difference inequality and one local Hedenmalm quotient value at every divisor point. -/
theorem continuedPrimeArchFormula_and_thetaValueConstraint_iff_rh_and_simple :
    ((∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
        riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
          0 ≤ ((continuedPrimeArchSourceRelativeTrace ((starRingEnd ℂ) z) -
            continuedPrimeArchSourceRelativeTrace z) /
              (z - (starRingEnd ℂ) z)).re) ∧
      XiThetaFirstQuotientValueConstraint) ↔
      RiemannHypothesis ∧ XiZerosSimple := by
  rw [continuedPrimeArchUpperCauchyFormula_iff_riemannHypothesis,
    xiThetaFirstQuotientValueConstraint_iff_simple]

/-- The conservative-metric existence interface is equivalently a pair of static value
constraints; the metric construction is not primitive data. -/
theorem continuedPrimeArch_and_thetaValueConstraint_iff_exists_conservative_metric :
    (ContinuedPrimeArchUpperCauchyDiagonalNonnegative ∧
      XiThetaFirstQuotientValueConstraint) ↔
      ∃ c : XiRealDivisorWeight, XiThetaMetricConservative c := by
  rw [continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_riemannHypothesis,
    xiThetaFirstQuotientValueConstraint_iff_simple,
    ← exists_conservative_xiThetaMetric_iff_rh_and_simple]

end

end RHTower
