import GaloisForLFunctions.RHTower.XiHedenmalmJordanNormalCollision
import GaloisForLFunctions.RHTower.XiHedenmalmThetaJetSource

/-!
# Xi Hedenmalm simplicity universality

The terminal simplicity classifiers for the continued Cauchy source, Hedenmalm quotient values,
de Branges Bezoutians, theta-evaluation density, local Jordan normality, and explicit theta-source
jets all carry the same multiplicity datum.  Adding the independent RH classifiers identifies the
corresponding Hermitian, self-adjoint, conservative-metric, and real-source phase.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Simultaneous realization of global Xi simplicity in every currently formalized local,
Hilbert-space, continuation, Bezoutian, and explicit theta-source chart. -/
def XiHedenmalmSimplicityUniversalCertificate : Prop :=
  XiThetaFirstQuotientValueConstraint ∧
  Dense (xiThetaEigenAlgebraicSubspace :
    Set (lp (fun _ : XiZeroCopy => ℂ) 2)) ∧
  XiContinuedCauchyToHedenmalmClosure ∧
  (∀ rho : XiDivisorSupport, XiLocalJordanNormal rho) ∧
  (∀ rho : XiDivisorSupport,
    xiHedenmalmBezoutian (xiSpectralPointSupport rho)
      (xiSpectralPointSupport rho) ≠ 0) ∧
  (∀ alpha : ℂ, XiC alpha = 0 →
    (∫ x : ℝ, thetaCuspFourierLaplaceDerivativeIntegrand alpha x) ≠ 0) ∧
  (∀ rho : XiDivisorSupport,
    (∀ j < 1,
      (∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand j
        (xiSpectralPointSupport rho) x) = 0) ∧
    (∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand 1
      (xiSpectralPointSupport rho) x) ≠ 0) ∧
  ∀ (rho : XiDivisorSupport) (x : ℝ),
    (∀ j < 1,
      iteratedDeriv j (thetaCuspBoundaryReflectionDefect x)
        (xiSpectralPointSupport rho) = 0) ∧
    iteratedDeriv 1 (thetaCuspBoundaryReflectionDefect x)
      (xiSpectralPointSupport rho) ≠ 0

/-- **Xi Hedenmalm simplicity universality law.**  Global Xi simplicity is equivalent to its
simultaneous realization in eight continuation, Hilbert, Jordan, Bezoutian, and theta-source
charts. -/
theorem xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate :
    XiZerosSimple ↔ XiHedenmalmSimplicityUniversalCertificate := by
  constructor
  · intro hsimple
    have hnormal : ∀ rho : XiDivisorSupport, XiLocalJordanNormal rho :=
      all_xiLocalJordanNormal_iff_simple.2 hsimple
    refine ⟨
      xiThetaFirstQuotientValueConstraint_iff_simple.2 hsimple,
      xiThetaEigenAlgebraicSubspace_dense_iff_simple.2 hsimple,
      xiContinuedCauchyToHedenmalmClosure_iff_simple.2 hsimple,
      hnormal,
      ?_,
      xiThetaFirstQuotientValueConstraint_iff_thetaCuspFourierLaplaceFirstMoment_ne_zero.1
        (xiThetaFirstQuotientValueConstraint_iff_simple.2 hsimple),
      ?_,
      ?_⟩
    · intro rho
      exact (xiHedenmalmBezoutian_self_ne_zero_iff_simple rho).2
        ((xiLocalJordanNormal_iff_multiplicity_one rho).1 (hnormal rho))
    · intro rho
      exact (xiSupportMultiplicity_eq_iff_thetaCuspFourierLaplaceJet rho 1).1
        ((xiLocalJordanNormal_iff_multiplicity_one rho).1 (hnormal rho))
    · intro rho x
      exact (xiSupportMultiplicity_eq_iff_thetaCuspBoundaryReflectionDefectJet
        rho x 1).1
        ((xiLocalJordanNormal_iff_multiplicity_one rho).1 (hnormal rho))
  · intro hcertificate
    exact xiThetaFirstQuotientValueConstraint_iff_simple.1 hcertificate.1

/-- Simultaneous RH-and-simplicity realization in the universal simplicity certificate, the
continued prime--Gamma sign, reciprocal self-adjointness, local Hermiticity, conservative metric,
and the positive-half theta source. -/
def XiHedenmalmRHSimplicityUniversalCertificate : Prop :=
  XiHedenmalmSimplicityUniversalCertificate ∧
  ContinuedPrimeArchUpperCauchyDiagonalNonnegative ∧
  IsSelfAdjoint xiReciprocalOperator ∧
  (∀ rho : XiDivisorSupport, (xiLocalJordanMatrix rho).IsHermitian) ∧
  (∃ c : XiRealDivisorWeight, XiThetaMetricConservative c) ∧
  ∀ t : ℝ, Xi t = 0 →
    (∫ x : ℝ in Ioi 0,
      x * thetaCuspFullSource x * Real.sin (t * x)) ≠ 0

/-- **RH--simplicity phase universality.**  RH plus simple Xi zeros is exactly the common phase
seen by all simplicity charts together with the prime--Gamma, reciprocal-operator, Hermitian
Jordan, conservative-metric, and real theta-source classifiers. -/
theorem riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate :
    (RiemannHypothesis ∧ XiZerosSimple) ↔
      XiHedenmalmRHSimplicityUniversalCertificate := by
  constructor
  · intro h
    have hsine :=
      (riemannHypothesis_and_xiZerosSimple_iff_thetaCuspFirstSineMoment).1 h
    exact ⟨
      xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate.1 h.2,
      continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_riemannHypothesis.2 h.1,
      xiReciprocalOperator_isSelfAdjoint_iff_rh.2 h.1,
      all_xiLocalJordanMatrix_isHermitian_iff_rh_and_simple.2 h,
      exists_conservative_xiThetaMetric_iff_rh_and_simple.2 h,
      hsine.2⟩
  · intro hcertificate
    exact ⟨
      continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_riemannHypothesis.1
        hcertificate.2.1,
      xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate.2
        hcertificate.1⟩

end

end RHTower
