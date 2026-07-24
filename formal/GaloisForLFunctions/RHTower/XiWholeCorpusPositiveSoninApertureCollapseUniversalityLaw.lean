import GaloisForLFunctions.RHTower.XiWholeCorpusPositivePhaseUniversalityLaw
import GaloisForLFunctions.RHTower.SoninCoupledPositiveApertureUniversalityLaw

/-!
# Xi whole-corpus positive Sonin aperture collapse

The complete Xi positive and failure phases previously collapsed only to proof-carrying
nondegenerate Sonin apertures.  The explicit prime-square residual makes every positive aperture
nondegenerate, so the whole-corpus classifications descend to the intrinsic positive-aperture
domain, both pointwise and simultaneously.
-/

namespace RHTower

noncomputable section

/-- **Whole-corpus/single positive-Sonin collapse.**  At every plain positive aperture, one
concrete relative determinant collar is exactly the complete Xi whole-corpus positive phase. -/
theorem
    wholeCorpusPositivePhaseUniversalCertificate_iff_singlePositiveSoninAperture
    {Lrect : ℝ} (hLrect : 0 < Lrect) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ Lrect ≤ Real.log n / 2)
    {eta Lsmooth : ℝ} (heta : 0 < eta) (hwindow : eta < Lsmooth - eta)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : IsRectangularSeparatedSourceSection Lrect P)
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    {degreeSet : Set ℕ} (hdegreeSet : degreeSet.Infinite)
    (prime : Nat.Primes) {q : ℕ} (hq : q ≠ 0)
    (a : SoninPositiveAperture) :
    XiWholeCorpusPositivePhaseUniversalCertificate
        Lrect N eta Lsmooth P D degreeSet prime q ↔
      UnitCollarExponentialEnvelope (fun n =>
        bernsteinCoefficientPurity
          (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment
            (soninCoupledNondegenerateAperture a)) n) :=
  (riemannHypothesis_iff_wholeCorpusPositivePhaseUniversalCertificate
    hLrect hN heta hwindow P hP hD hdegreeSet prime hq).symm.trans
      (riemannHypothesis_iff_soninPositiveApertureRelativeDeterminant_unitCollar a)

/-- The complete Xi whole-corpus positive phase is equivalent to simultaneous determinant
collars over every plain positive Sonin aperture. -/
theorem
    wholeCorpusPositivePhaseUniversalCertificate_iff_allPositiveSoninApertures
    {Lrect : ℝ} (hLrect : 0 < Lrect) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ Lrect ≤ Real.log n / 2)
    {eta Lsmooth : ℝ} (heta : 0 < eta) (hwindow : eta < Lsmooth - eta)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : IsRectangularSeparatedSourceSection Lrect P)
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    {degreeSet : Set ℕ} (hdegreeSet : degreeSet.Infinite)
    (prime : Nat.Primes) {q : ℕ} (hq : q ≠ 0) :
    XiWholeCorpusPositivePhaseUniversalCertificate
        Lrect N eta Lsmooth P D degreeSet prime q ↔
      SoninAllPositiveApertureUnitCollarPhase :=
  (riemannHypothesis_iff_wholeCorpusPositivePhaseUniversalCertificate
    hLrect hN heta hwindow P hP hD hdegreeSet prime hq).symm.trans
      (primeArchSourceMomentHankelExactReconstructionPhase_iff_riemannHypothesis.symm.trans
        primeArchSourceMomentHankelExactReconstructionPhase_iff_allSoninPositiveApertureUnitCollarPhase)

/-- Whole-corpus failure is exactly collar failure at any chosen plain positive Sonin
aperture. -/
theorem
    wholeCorpusFailurePhaseUniversalCertificate_iff_not_singlePositiveSoninAperture
    {Lrect : ℝ} (hLrect : 0 < Lrect) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ Lrect ≤ Real.log n / 2)
    {eta Lsmooth : ℝ} (heta : 0 < eta) (hwindow : eta < Lsmooth - eta)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : IsRectangularSeparatedSourceSection Lrect P)
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    {degreeSet : Set ℕ} (hdegreeSet : degreeSet.Infinite)
    (prime : Nat.Primes) {q : ℕ} (hq : q ≠ 0)
    {aperture : ℝ} (haperture : 0 < aperture)
    (a : SoninPositiveAperture) :
    XiWholeCorpusFailurePhaseUniversalCertificate
        Lrect N eta Lsmooth P D degreeSet prime q aperture ↔
      ¬UnitCollarExponentialEnvelope (fun n =>
        bernsteinCoefficientPurity
          (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment
            (soninCoupledNondegenerateAperture a)) n) :=
  (not_riemannHypothesis_iff_wholeCorpusFailurePhaseUniversalCertificate
    hLrect hN heta hwindow P hP hD hdegreeSet prime hq haperture).symm.trans
      (not_congr
        (riemannHypothesis_iff_soninPositiveApertureRelativeDeterminant_unitCollar a))

/-- The complete Xi whole-corpus failure phase is equivalent to synchronized determinant-collar
failure over every plain positive Sonin aperture. -/
theorem
    wholeCorpusFailurePhaseUniversalCertificate_iff_allPositiveSoninApertureFailures
    {Lrect : ℝ} (hLrect : 0 < Lrect) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ Lrect ≤ Real.log n / 2)
    {eta Lsmooth : ℝ} (heta : 0 < eta) (hwindow : eta < Lsmooth - eta)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : IsRectangularSeparatedSourceSection Lrect P)
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    {degreeSet : Set ℕ} (hdegreeSet : degreeSet.Infinite)
    (prime : Nat.Primes) {q : ℕ} (hq : q ≠ 0)
    {aperture : ℝ} (haperture : 0 < aperture) :
    XiWholeCorpusFailurePhaseUniversalCertificate
        Lrect N eta Lsmooth P D degreeSet prime q aperture ↔
      SoninAllPositiveApertureUnitCollarFailurePhase :=
  (not_riemannHypothesis_iff_wholeCorpusFailurePhaseUniversalCertificate
    hLrect hN heta hwindow P hP hD hdegreeSet prime hq haperture).symm.trans
      ((not_congr
        primeArchSourceMomentHankelExactReconstructionPhase_iff_riemannHypothesis).symm.trans
          not_primeArchSourceMomentHankelExactReconstructionPhase_iff_allSoninPositiveApertureUnitCollarFailurePhase)

end

end RHTower
