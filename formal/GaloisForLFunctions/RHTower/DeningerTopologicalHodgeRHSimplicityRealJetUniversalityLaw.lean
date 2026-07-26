import GaloisForLFunctions.RHTower.DeningerArithmeticJordanObstruction
import GaloisForLFunctions.RHTower.DeningerCompactOpenGradedRealJetUniversalityLaw
import GaloisForLFunctions.RHTower.XiHedenmalmSimplicityUniversalityLaw
import GaloisForLFunctions.RHTower.XiWholeCorpusPositivePhaseUniversalityLaw

/-!
# Deninger topological-Hodge RH/simplicity Real-jet universality

A direct positive compact-open Hodge star forces both RH and simple Xi zeros.  The resulting
joint phase is simultaneously visible in every Hedenmalm, prime--Gamma, reciprocal-operator,
Hermitian-Jordan, conservative-metric, and theta-source chart, while compact-open cohomology
carries its exact graded Real involution.
-/

open Complex

namespace RHTower

noncomputable section

/-- The Jordan obstruction upgrades a direct topological Hodge star from pointwise multiplicity
one to global Xi simplicity. -/
theorem DeningerArithmeticTopologicalHodgeStar.xiZerosSimple
    (Hodge : DeningerArithmeticTopologicalHodgeStar) :
    XiZerosSimple := by
  apply all_xiLocalJordanNormal_iff_simple.mp
  intro rho
  exact (xiLocalJordanNormal_iff_multiplicity_one rho).2
    (Hodge.xiSupportMultiplicity_eq_one rho)

/-- Complete RH, simplicity, topology, and graded Real-jet output of the direct compact-open Hodge
model. -/
structure DeningerTopologicalHodgeRHSimplicityRealJetCertificate : Prop where
  riemannHypothesis : RiemannHypothesis
  xiZerosSimple : XiZerosSimple
  allLocalJordanNormal :
    ∀ rho : XiDivisorSupport, XiLocalJordanNormal rho
  hedenmalmRHSimplicityCharts :
    XiHedenmalmRHSimplicityUniversalCertificate
  wholeCorpusPositivePhase :
    ∀ {Lrect : ℝ}, 0 < Lrect →
      ∀ {N : ℕ}, (∀ n : ℕ, N ≤ n →
        1 ≤ n ∧ Lrect ≤ Real.log n / 2) →
      ∀ {eta Lsmooth : ℝ}, 0 < eta → eta < Lsmooth - eta →
      ∀ (P : ℕ → XiSeparatedContinuedCauchyPacket),
        IsRectangularSeparatedSourceSection Lrect P →
      ∀ {D : ℕ → ℕ}, XiCTaylorOddThetaTailSuperaccurateSchedule D →
      ∀ {degreeSet : Set ℕ}, degreeSet.Infinite →
      ∀ (prime : Nat.Primes) {q : ℕ}, q ≠ 0 →
        XiWholeCorpusPositivePhaseUniversalCertificate
          Lrect N eta Lsmooth P D degreeSet prime q
  compactOpenRealInvolutive :
    ∀ x : DeningerArithmeticCompactOpenH1,
      deningerArithmeticCompactOpenH1EvenSigma
          (deningerArithmeticCompactOpenH1EvenSigma x) = x
  xiJetGradedReal :
    ∀ (F : DeningerCompactOpenEntire)
        (rho : XiDivisorSupport) (k : ℕ),
      deningerCompactOpenJet (xiSpectralPointSupport rho) k
          (deningerCompactOpenFunctionalEquationSigma F) =
        (-1 : ℂ) ^ k *
          (starRingEnd ℂ)
            (deningerCompactOpenJet
              (xiSpectralPointSupport (xiZeroConjEquiv rho)) k F)

/-- **Deninger topological-Hodge RH/simplicity Real-jet universality law.** -/
theorem deningerTopologicalHodge_rhSimplicityRealJetUniversality
    (Hodge : DeningerArithmeticTopologicalHodgeStar) :
    DeningerTopologicalHodgeRHSimplicityRealJetCertificate := by
  have hRH :=
    DeningerArithmeticTopologicalHodgeStar.riemannHypothesis Hodge
  have hsimple : XiZerosSimple := Hodge.xiZerosSimple
  have hnormal :
      ∀ rho : XiDivisorSupport, XiLocalJordanNormal rho :=
    all_xiLocalJordanNormal_iff_simple.mpr hsimple
  have hgraded := deninger_compactOpen_gradedRealJetUniversality
  exact
    { riemannHypothesis := hRH
      xiZerosSimple := hsimple
      allLocalJordanNormal := hnormal
      hedenmalmRHSimplicityCharts :=
        riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate.mp
          ⟨hRH, hsimple⟩
      wholeCorpusPositivePhase :=
        fun hLrect hN heta hwindow P hP hD hdegreeSet prime hq =>
          (riemannHypothesis_iff_wholeCorpusPositivePhaseUniversalCertificate
            hLrect hN heta hwindow P hP hD hdegreeSet prime hq).mp hRH
      compactOpenRealInvolutive := hgraded.2.2.1
      xiJetGradedReal := hgraded.2.2.2 }

end

end RHTower
