import GaloisForLFunctions.RHTower.HedenmalmThetaAnomalyWardKreinPythagoreanDefect
import GaloisForLFunctions.RHTower.HedenmalmThetaPrimeRankTwoCorrectionNoGo

/-!
# Ward realification as functional-equation pair polarization

Critical-line conjugation sends centered spectral coordinate `z` to `conj(z)`.  This module proves
that P-G123 Ward realification is exactly the invariant average of genuine line-conjugate Xi
copies, while Ward anomaly is exactly their anti-invariant half-difference.

Completed first-divided multiplicity energy and Burnol frame energy are separately invariant under
line conjugation, hence so is Ward mass.  Raw pair numerators decompose into symmetric realified
sector and antisymmetric anomaly sector.  This supplies exact functional-equation provenance for
the source anomaly but also closes reflection averaging as an RH producer: pairing constructs the
projection; it does not force a paired point to be fixed.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace RHTower

open HedenmalmThetaSource

/-- Completed first-divided Xi multiplicity energy is invariant under critical-line conjugation. -/
theorem norm_sq_completedXiFirstDividedL2_lineConj (q : XiZeroCopy) :
    ‖completedXiFirstDividedL2 (xiZeroCopyLineConjEquiv q).1‖ ^ 2 =
      ‖completedXiFirstDividedL2 q.1‖ ^ 2 := by
  rw [norm_sq_completedXiFirstDividedL2_eq_sameFiberThetaRootEnergy,
    norm_sq_completedXiFirstDividedL2_eq_sameFiberThetaRootEnergy]
  have hroot := thetaXiRootEnergy_lineConj q
  rw [show thetaRootEnergy
      (xiSpectralPointSupport (xiZeroCopyLineConjEquiv q).1) =
        thetaRootEnergy (xiSpectralPointSupport q.1) by
    simpa only [thetaXiRootEnergy, xiSpectralPoint_eq_support] using hroot]

/-- Genuine multiplicity-scaled Ward mass is line-conjugation invariant. -/
theorem thetaXiWardRealificationMass_lineConj (q : XiZeroCopy) :
    thetaXiWardRealificationMass (xiZeroCopyLineConjEquiv q) =
      thetaXiWardRealificationMass q := by
  rw [thetaXiWardRealificationMass, thetaXiWardRealificationMass,
    xiSpectralPoint_lineConj, burnolTwoPrimeFrameEnergy_conj,
    norm_sq_completedXiFirstDividedL2_lineConj]

/-- Raw numerator on line-conjugate partner uses conjugate spectral coordinate and same mass. -/
theorem thetaXiWardRawNumerator_lineConj (q : XiZeroCopy) :
    thetaXiWardRawNumerator (xiZeroCopyLineConjEquiv q) =
      -(starRingEnd ℂ) (xiSpectralPoint q) *
        (thetaXiWardRealificationMass q : ℂ) := by
  rw [thetaXiWardRawNumerator_eq, xiSpectralPoint_lineConj,
    thetaXiWardRealificationMass_lineConj]

/-! ## Symmetric and antisymmetric pair sectors -/

/-- **Functional-equation average law.**  Ward-realified numerator is pair-symmetric average. -/
theorem thetaXiWardRealifiedNumerator_eq_lineConj_pairAverage (q : XiZeroCopy) :
    thetaXiWardRealifiedNumerator q =
      (thetaXiWardRawNumerator q +
        thetaXiWardRawNumerator (xiZeroCopyLineConjEquiv q)) / 2 := by
  rw [thetaXiWardRawNumerator_eq, thetaXiWardRawNumerator_lineConj,
    thetaXiWardRealifiedNumerator_eq]
  have havg :
      (xiSpectralPoint q + (starRingEnd ℂ) (xiSpectralPoint q)) / 2 =
        ((xiSpectralPoint q).re : ℂ) := by
    apply Complex.ext <;> norm_num
  rw [← havg]
  ring

/-- **Functional-equation difference law.**  Ward anomaly is pair-antisymmetric half-difference. -/
theorem thetaXiWardRealificationAnomaly_eq_lineConj_pairHalfDifference
    (q : XiZeroCopy) :
    thetaXiWardRealificationAnomaly q =
      (thetaXiWardRawNumerator (xiZeroCopyLineConjEquiv q) -
        thetaXiWardRawNumerator q) / 2 := by
  rw [thetaXiWardRawNumerator_lineConj, thetaXiWardRawNumerator_eq,
    thetaXiWardRealificationAnomaly_eq]
  have hdiff :
      xiSpectralPoint q - (starRingEnd ℂ) (xiSpectralPoint q) =
        2 * Complex.I * ((xiSpectralPoint q).im : ℂ) := by
    rw [Complex.ext_iff]
    constructor
    · norm_num
    · norm_num
      ring
  calc
    Complex.I * ((xiSpectralPoint q).im : ℂ) *
          (thetaXiWardRealificationMass q : ℂ) =
        ((2 * Complex.I * ((xiSpectralPoint q).im : ℂ)) *
          (thetaXiWardRealificationMass q : ℂ)) / 2 := by ring
    _ = ((xiSpectralPoint q - (starRingEnd ℂ) (xiSpectralPoint q)) *
          (thetaXiWardRealificationMass q : ℂ)) / 2 := by rw [hdiff]
    _ = (-((starRingEnd ℂ) (xiSpectralPoint q)) *
            (thetaXiWardRealificationMass q : ℂ) -
          -xiSpectralPoint q * (thetaXiWardRealificationMass q : ℂ)) / 2 := by ring

/-- Ward anomaly reverses orientation on line-conjugate partner. -/
theorem thetaXiWardRealificationAnomaly_lineConj (q : XiZeroCopy) :
    thetaXiWardRealificationAnomaly (xiZeroCopyLineConjEquiv q) =
      -thetaXiWardRealificationAnomaly q := by
  rw [thetaXiWardRealificationAnomaly_eq, thetaXiWardRealificationAnomaly_eq,
    xiSpectralPoint_lineConj, Complex.conj_im, thetaXiWardRealificationMass_lineConj]
  push_cast
  ring

/-- Ward-realified numerator is invariant under line conjugation. -/
theorem thetaXiWardRealifiedNumerator_lineConj (q : XiZeroCopy) :
    thetaXiWardRealifiedNumerator (xiZeroCopyLineConjEquiv q) =
      thetaXiWardRealifiedNumerator q := by
  rw [thetaXiWardRealifiedNumerator_eq, thetaXiWardRealifiedNumerator_eq,
    xiSpectralPoint_lineConj, Complex.conj_re, thetaXiWardRealificationMass_lineConj]

/-- Normalized Ward realification is average of raw universal connections on a genuine
line-conjugate Xi pair. -/
theorem thetaXiWardRealifiedConnection_eq_lineConj_connectionAverage (q : XiZeroCopy) :
    thetaXiWardRealifiedConnection q =
      (burnolMultiplicativeJetSpectralConnection (xiSpectralPoint q) +
        burnolMultiplicativeJetSpectralConnection
          (xiSpectralPoint (xiZeroCopyLineConjEquiv q))) / 2 := by
  rw [thetaXiWardRealifiedConnection_eq,
    burnolMultiplicativeJetSpectralConnection_eq,
    burnolMultiplicativeJetSpectralConnection_eq,
    xiSpectralPoint_lineConj]
  apply Complex.ext <;> norm_num

/-! ## Pair-collapse boundary -/

/-- Raw pair numerators agree exactly when their antisymmetric Ward anomaly vanishes. -/
theorem thetaXiWardRawNumerator_lineConj_eq_iff_anomaly_eq_zero (q : XiZeroCopy) :
    thetaXiWardRawNumerator (xiZeroCopyLineConjEquiv q) =
        thetaXiWardRawNumerator q ↔
      thetaXiWardRealificationAnomaly q = 0 := by
  constructor
  · intro h
    rw [thetaXiWardRealificationAnomaly_eq_lineConj_pairHalfDifference, h,
      sub_self, zero_div]
  · intro h
    rw [thetaXiWardRealificationAnomaly_eq_lineConj_pairHalfDifference] at h
    have hdiff :
        thetaXiWardRawNumerator (xiZeroCopyLineConjEquiv q) -
          thetaXiWardRawNumerator q = 0 := by
      rcases (div_eq_zero_iff).mp h with hdiff | htwo
      · exact hdiff
      · norm_num at htwo
    exact sub_eq_zero.mp hdiff

/-- Pair collapse is exactly critical-line placement on one Xi copy. -/
theorem thetaXiWardRawNumerator_lineConj_eq_iff_line (q : XiZeroCopy) :
    thetaXiWardRawNumerator (xiZeroCopyLineConjEquiv q) =
        thetaXiWardRawNumerator q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [thetaXiWardRawNumerator_lineConj_eq_iff_anomaly_eq_zero,
    thetaXiWardRealificationAnomaly_eq_zero_iff, xiSpectralPoint_im_eq]
  constructor <;> intro h <;> linarith

/-- Global collapse of all line-conjugate raw numerator pairs is exactly RH. -/
theorem all_thetaXiWardRawNumerator_lineConj_eq_iff_riemannHypothesis :
    (∀ q : XiZeroCopy,
      thetaXiWardRawNumerator (xiZeroCopyLineConjEquiv q) =
        thetaXiWardRawNumerator q) ↔ RiemannHypothesis := by
  rw [← all_thetaXiWardRealifiedConnections_eq_spectral_iff_riemannHypothesis]
  constructor
  · intro h q
    exact (thetaXiWardRealifiedConnection_eq_spectral_iff_line q).mpr
      ((thetaXiWardRawNumerator_lineConj_eq_iff_line q).mp (h q))
  · intro h q
    exact (thetaXiWardRawNumerator_lineConj_eq_iff_line q).mpr
      ((thetaXiWardRealifiedConnection_eq_spectral_iff_line q).mp (h q))

end RHTower
