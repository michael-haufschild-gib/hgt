import GaloisForLFunctions.RHTower.XiHedenmalmSimplicityUniversalityLaw
import GaloisForLFunctions.RHTower.XiWholeCorpusPositivePhaseUniversalityLaw

/-!
# Whole-corpus Hedenmalm simplicity universality

The whole-corpus certificate already carries exactly the RH phase, while the Hedenmalm simplicity
certificate carries exactly the multiplicity-one phase across its continuation, Hilbert, Jordan,
Bezoutian, and theta-source charts.  Their product therefore closes the previously separate
RH-and-simplicity interface.
-/

namespace RHTower

noncomputable section

/-- **Whole-corpus Hedenmalm simplicity universality law.** The complete Xi positive phase
together with simple Xi zeros is exactly the full RH-and-simplicity Hedenmalm certificate. -/
theorem wholeCorpusPositivePhase_and_xiZerosSimple_iff_hendenmalmUniversalCertificate
    {Lrect : ℝ} (hLrect : 0 < Lrect) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ Lrect ≤ Real.log n / 2)
    {eta Lsmooth : ℝ} (heta : 0 < eta) (hwindow : eta < Lsmooth - eta)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : IsRectangularSeparatedSourceSection Lrect P)
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    {degreeSet : Set ℕ} (hdegreeSet : degreeSet.Infinite)
    (prime : Nat.Primes) {q : ℕ} (hq : q ≠ 0) :
    (XiWholeCorpusPositivePhaseUniversalCertificate
        Lrect N eta Lsmooth P D degreeSet prime q ∧ XiZerosSimple) ↔
      XiHedenmalmRHSimplicityUniversalCertificate :=
  (and_congr
    (riemannHypothesis_iff_wholeCorpusPositivePhaseUniversalCertificate
      hLrect hN heta hwindow P hP hD hdegreeSet prime hq).symm
    Iff.rfl).trans
      riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate

/-- Once the whole-corpus phase is known, the explicit RH conjunct in the terminal Hedenmalm
certificate is discharged: global Xi simplicity alone is equivalent to the full certificate. -/
theorem xiZerosSimple_iff_hendenmalmUniversalCertificate_of_wholeCorpusPositivePhase
    {Lrect : ℝ} {N : ℕ} {eta Lsmooth : ℝ}
    {P : ℕ → XiSeparatedContinuedCauchyPacket}
    {D : ℕ → ℕ} {degreeSet : Set ℕ} {prime : Nat.Primes} {q : ℕ}
    (hwhole : XiWholeCorpusPositivePhaseUniversalCertificate
      Lrect N eta Lsmooth P D degreeSet prime q) :
    XiZerosSimple ↔ XiHedenmalmRHSimplicityUniversalCertificate := by
  constructor
  · intro hsimple
    have hRH :=
      riemannHypothesis_iff_terminalGeometricPhaseUniversalCertificate.2
        hwhole.geometricPhase
    exact
      riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate.1
        ⟨hRH, hsimple⟩
  · intro hcertificate
    exact
      (riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate.2
        hcertificate).2

/-- Under the whole-corpus phase, the eight-chart simplicity certificate and the enlarged
RH-and-simplicity Hedenmalm certificate are the same proposition. -/
theorem hendenmalmSimplicityUniversalCertificate_iff_rhSimplicity_of_wholeCorpusPositivePhase
    {Lrect : ℝ} {N : ℕ} {eta Lsmooth : ℝ}
    {P : ℕ → XiSeparatedContinuedCauchyPacket}
    {D : ℕ → ℕ} {degreeSet : Set ℕ} {prime : Nat.Primes} {q : ℕ}
    (hwhole : XiWholeCorpusPositivePhaseUniversalCertificate
      Lrect N eta Lsmooth P D degreeSet prime q) :
    XiHedenmalmSimplicityUniversalCertificate ↔
      XiHedenmalmRHSimplicityUniversalCertificate :=
  xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate.symm.trans
    (xiZerosSimple_iff_hendenmalmUniversalCertificate_of_wholeCorpusPositivePhase hwhole)

/-- **Whole-corpus Hedenmalm failure classification.** The enlarged RH-and-simplicity certificate
fails exactly because the whole-corpus RH phase fails or because Xi has a multiple zero. -/
theorem wholeCorpusFailurePhase_or_not_xiZerosSimple_iff_not_hendenmalmUniversalCertificate
    {Lrect : ℝ} (hLrect : 0 < Lrect) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ Lrect ≤ Real.log n / 2)
    {eta Lsmooth : ℝ} (heta : 0 < eta) (hwindow : eta < Lsmooth - eta)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : IsRectangularSeparatedSourceSection Lrect P)
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    {degreeSet : Set ℕ} (hdegreeSet : degreeSet.Infinite)
    (prime : Nat.Primes) {q : ℕ} (hq : q ≠ 0)
    {aperture : ℝ} (haperture : 0 < aperture) :
    (XiWholeCorpusFailurePhaseUniversalCertificate
          Lrect N eta Lsmooth P D degreeSet prime q aperture ∨
        ¬XiZerosSimple) ↔
      ¬XiHedenmalmRHSimplicityUniversalCertificate := by
  constructor
  · intro hfailure hcertificate
    have hphase :=
      riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate.2
        hcertificate
    rcases hfailure with hwholeFailure | hnotSimple
    · exact
        (not_riemannHypothesis_iff_wholeCorpusFailurePhaseUniversalCertificate
          hLrect hN heta hwindow P hP hD hdegreeSet prime hq haperture).2
            hwholeFailure hphase.1
    · exact hnotSimple hphase.2
  · intro hnotCertificate
    by_cases hsimple : XiZerosSimple
    · left
      apply
        (not_riemannHypothesis_iff_wholeCorpusFailurePhaseUniversalCertificate
          hLrect hN heta hwindow P hP hD hdegreeSet prime hq haperture).1
      intro hRH
      exact hnotCertificate
        (riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate.1
          ⟨hRH, hsimple⟩)
    · exact Or.inr hsimple

/-- Certificate-only negative form: failure of the full RH-simplicity phase is exactly
whole-corpus failure or failure of the eight-chart Hedenmalm simplicity phase. -/
theorem
    wholeCorpusFailurePhase_or_not_hendenmalmSimplicity_iff_not_rhSimplicityCertificate
    {Lrect : ℝ} (hLrect : 0 < Lrect) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ Lrect ≤ Real.log n / 2)
    {eta Lsmooth : ℝ} (heta : 0 < eta) (hwindow : eta < Lsmooth - eta)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : IsRectangularSeparatedSourceSection Lrect P)
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    {degreeSet : Set ℕ} (hdegreeSet : degreeSet.Infinite)
    (prime : Nat.Primes) {q : ℕ} (hq : q ≠ 0)
    {aperture : ℝ} (haperture : 0 < aperture) :
    (XiWholeCorpusFailurePhaseUniversalCertificate
          Lrect N eta Lsmooth P D degreeSet prime q aperture ∨
        ¬XiHedenmalmSimplicityUniversalCertificate) ↔
      ¬XiHedenmalmRHSimplicityUniversalCertificate :=
  (or_congr Iff.rfl
    (not_congr xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate).symm).trans
      (wholeCorpusFailurePhase_or_not_xiZerosSimple_iff_not_hendenmalmUniversalCertificate
        hLrect hN heta hwindow P hP hD hdegreeSet prime hq haperture)

end

end RHTower
