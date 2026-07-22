import GaloisForLFunctions.RHTower.PrimeArchThetaHankelDegreeTail
import GaloisForLFunctions.RHTower.XiGuinandWeilFiniteHermiteCriterion
import GaloisForLFunctions.RHTower.XiTraceHankelCountableCriterion

/-!
# Xi countable Hankel test-set universality

The central divisor, prime--archimedean source, and finite Guinand--Weil contour models admit
apparently different reductions of their full Hankel positivity cones.  In fact all reductions
are exact at once: integer tests and their scalar-limit form, every fixed degree tail, tests on
every infinite exact-degree set, their monic and fixed Eisenstein subfamilies, and rational
rectangle/integer-Hermite contours all carry the same datum as the full real Hermite family.
-/

namespace RHTower

noncomputable section

/-- Simultaneous realization of every countable, cofinal, sparse-degree, irreducible, and full
Hermite presentation of the Xi Hankel positivity cone. -/
structure XiCountableHankelTestSetUniversalCertificate : Prop where
  centralIntegerTests : XiCentralTraceHankelIntNonnegative
  centralIntegerLimitTests : XiCentralTraceHankelIntNonnegativeLimit
  primeArchIntegerTests : PrimeArchSourceTraceHankelIntNonnegative
  everyDegreeTail :
    ∀ K : ℕ, PrimeArchSourceTraceHankelIntDegreeTailNonnegativeFrom K
  everyInfiniteDegreeSet :
    ∀ D : Set ℕ, D.Infinite →
      PrimeArchSourceTraceHankelIntDegreeSetNonnegative D
  everyMonicInfiniteDegreeSet :
    ∀ D : Set ℕ, D.Infinite →
      PrimeArchSourceTraceHankelIntMonicDegreeSetNonnegative D
  everyTwoEisensteinInfiniteDegreeSet :
    ∀ D : Set ℕ, D.Infinite →
      PrimeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative D
  fullSymmetricHermiteContours : XiSymmetricPrimeArchTraceHankelNonnegative
  countableSymmetricHermiteContours :
    XiCountableSymmetricPrimeArchTraceHankelNonnegative

/-- **Xi countable Hankel test-set universality law.**  RH is equivalent to simultaneous
positivity in all nine test presentations.  In particular the countable rational-rectangle,
integer-Hermite interface recovers every full real contour test and every sparse polynomial
presentation, including all monic `2`-Eisenstein families on all infinite degree sets. -/
theorem riemannHypothesis_iff_countableHankelTestSetUniversalCertificate :
    RiemannHypothesis ↔ XiCountableHankelTestSetUniversalCertificate := by
  constructor
  · intro hRH
    exact {
      centralIntegerTests :=
        xiCentralTraceHankelIntNonnegative_iff_riemannHypothesis.2 hRH
      centralIntegerLimitTests :=
        xiCentralTraceHankelIntNonnegativeLimit_iff_riemannHypothesis.2 hRH
      primeArchIntegerTests :=
        primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis.2 hRH
      everyDegreeTail := fun K =>
        (primeArchSourceTraceHankelIntDegreeTailNonnegativeFrom_iff_riemannHypothesis K).2 hRH
      everyInfiniteDegreeSet := fun D hD =>
        (primeArchSourceTraceHankelIntDegreeSetNonnegative_iff_riemannHypothesis hD).2 hRH
      everyMonicInfiniteDegreeSet := fun D hD =>
        (primeArchSourceTraceHankelIntMonicDegreeSetNonnegative_iff_riemannHypothesis hD).2 hRH
      everyTwoEisensteinInfiniteDegreeSet := fun D hD =>
        (primeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative_iff_riemannHypothesis
          hD).2 hRH
      fullSymmetricHermiteContours :=
        symmetricPrimeArchTraceHankelNonnegative_iff_riemannHypothesis.2 hRH
      countableSymmetricHermiteContours :=
        countableSymmetricPrimeArchTraceHankelNonnegative_iff_riemannHypothesis.2 hRH }
  · intro hcertificate
    exact countableSymmetricPrimeArchTraceHankelNonnegative_iff_riemannHypothesis.1
      hcertificate.countableSymmetricHermiteContours

/-- Rational rectangles and integer Hermite polynomials are already a complete test set for the
full real symmetric finite-Hermite contour condition. -/
theorem countableSymmetricPrimeArchTraceHankelNonnegative_iff_full :
    XiCountableSymmetricPrimeArchTraceHankelNonnegative ↔
      XiSymmetricPrimeArchTraceHankelNonnegative := by
  rw [countableSymmetricPrimeArchTraceHankelNonnegative_iff_riemannHypothesis,
    symmetricPrimeArchTraceHankelNonnegative_iff_riemannHypothesis]

/-- Failure is likewise test-set independent: every proposed cofinal or countable presentation
fails simultaneously. -/
structure XiCountableHankelTestSetFailureUniversalCertificate : Prop where
  centralIntegerTestsFail : ¬ XiCentralTraceHankelIntNonnegative
  centralIntegerLimitTestsFail : ¬ XiCentralTraceHankelIntNonnegativeLimit
  primeArchIntegerTestsFail : ¬ PrimeArchSourceTraceHankelIntNonnegative
  everyDegreeTailFails :
    ∀ K : ℕ, ¬ PrimeArchSourceTraceHankelIntDegreeTailNonnegativeFrom K
  everyInfiniteDegreeSetFails :
    ∀ D : Set ℕ, D.Infinite →
      ¬ PrimeArchSourceTraceHankelIntDegreeSetNonnegative D
  everyMonicInfiniteDegreeSetFails :
    ∀ D : Set ℕ, D.Infinite →
      ¬ PrimeArchSourceTraceHankelIntMonicDegreeSetNonnegative D
  everyTwoEisensteinInfiniteDegreeSetFails :
    ∀ D : Set ℕ, D.Infinite →
      ¬ PrimeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative D
  fullSymmetricHermiteContoursFail : ¬ XiSymmetricPrimeArchTraceHankelNonnegative
  countableSymmetricHermiteContoursFail :
    ¬ XiCountableSymmetricPrimeArchTraceHankelNonnegative

/-- **Synchronized countable-test failure law.**  Failure of RH is equivalent to simultaneous
failure of every member of every sparse family, not merely failure of one chosen full cone. -/
theorem not_riemannHypothesis_iff_countableHankelTestSetFailureUniversalCertificate :
    ¬ RiemannHypothesis ↔ XiCountableHankelTestSetFailureUniversalCertificate := by
  constructor
  · intro hnotRH
    exact {
      centralIntegerTestsFail := fun h => hnotRH
        (xiCentralTraceHankelIntNonnegative_iff_riemannHypothesis.1 h)
      centralIntegerLimitTestsFail := fun h => hnotRH
        (xiCentralTraceHankelIntNonnegativeLimit_iff_riemannHypothesis.1 h)
      primeArchIntegerTestsFail := fun h => hnotRH
        (primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis.1 h)
      everyDegreeTailFails := fun K h => hnotRH
        ((primeArchSourceTraceHankelIntDegreeTailNonnegativeFrom_iff_riemannHypothesis K).1 h)
      everyInfiniteDegreeSetFails := fun D hD h => hnotRH
        ((primeArchSourceTraceHankelIntDegreeSetNonnegative_iff_riemannHypothesis hD).1 h)
      everyMonicInfiniteDegreeSetFails := fun D hD h => hnotRH
        ((primeArchSourceTraceHankelIntMonicDegreeSetNonnegative_iff_riemannHypothesis hD).1 h)
      everyTwoEisensteinInfiniteDegreeSetFails := fun D hD h => hnotRH
        ((primeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative_iff_riemannHypothesis
          hD).1 h)
      fullSymmetricHermiteContoursFail := fun h => hnotRH
        (symmetricPrimeArchTraceHankelNonnegative_iff_riemannHypothesis.1 h)
      countableSymmetricHermiteContoursFail := fun h => hnotRH
        (countableSymmetricPrimeArchTraceHankelNonnegative_iff_riemannHypothesis.1 h) }
  · intro hfailure hRH
    exact hfailure.countableSymmetricHermiteContoursFail
      (countableSymmetricPrimeArchTraceHankelNonnegative_iff_riemannHypothesis.2 hRH)

/-- Positive and failure test-set phases are exact complements. -/
theorem not_countableHankelTestSetUniversalCertificate_iff_failure :
    ¬ XiCountableHankelTestSetUniversalCertificate ↔
      XiCountableHankelTestSetFailureUniversalCertificate := by
  constructor
  · intro hnotCertificate
    apply not_riemannHypothesis_iff_countableHankelTestSetFailureUniversalCertificate.1
    intro hRH
    exact hnotCertificate
      (riemannHypothesis_iff_countableHankelTestSetUniversalCertificate.1 hRH)
  · intro hfailure hcertificate
    have hnotRH :=
      not_riemannHypothesis_iff_countableHankelTestSetFailureUniversalCertificate.2 hfailure
    exact hnotRH
      (riemannHypothesis_iff_countableHankelTestSetUniversalCertificate.2 hcertificate)

end

end RHTower
