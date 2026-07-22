import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniJensenSourceLaw
import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniPairQuotient
import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniGlobalJensenLaw
import GaloisForLFunctions.RHTower.XiSquaredSeamPowerSixtyFourMassCriterion

/-!
# Xi squared-seam Cassini--dyadic universality

The unconditional entire Cassini quotient and its exact reflection-pair/Jensen transport coexist
with a single squared-seam transverse orientation datum.  Vanishing of one scalar charge
synchronizes every dyadic tail, every shifted Hankel cutoff, and the power-64
Hermitian/prime--Gamma mass boundary.  The complementary theorem packages strict scalar and
explicit dyadic/Hankel witnesses.
-/

open Complex Polynomial Set
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

/-- Unconditional entire-source, zero-exhaustion, multiplicity, pair-quotient, Jensen, and radial
mass realization of the shift-one Cassini coordinate. -/
def XiSquaredSeamCassiniUniversalSourceCertificate : Prop :=
  (∀ z : ℂ, xiSquaredSeamEntireQuotient (z ^ 2) = XiC z) ∧
  (∀ u : ℂ, xiSquaredSeamCassiniSource u = 0 ↔
    ∃ q : XiZeroCopy, xiSquaredSeamCassiniZero q = u) ∧
  (∀ q : XiZeroCopy,
    analyticOrderAt xiSquaredSeamCassiniSource (xiSquaredSeamCassiniZero q) =
      Int.toNat ((MeromorphicOn.divisor xi Set.univ) (q.1 : ℂ))) ∧
  (∀ F : ℂ → ℝ≥0∞,
    (∑' q : XiZeroCopy, F (xiSquaredSeamCassiniZero q)) =
      2 * ∑' c : XiSquaredSeamCassiniZeroCopy, F c.1.1) ∧
  (∀ r : ℝ, 0 < r → 0 ≤ xiSquaredSeamCassiniJensenExcess r) ∧
  xiSquaredSeamPowerSixtyFourJensenDivisorIntegral =
    ENNReal.ofReal (xiSquaredSeamPowerSixtyFourHermitianMass / 4096)

/-- The Cassini entire source and all its exact divisor transports exist unconditionally. -/
theorem xiSquaredSeamCassiniUniversalSourceCertificate_proof :
    XiSquaredSeamCassiniUniversalSourceCertificate := by
  exact ⟨
    xiSquaredSeamEntireQuotient_sq,
    xiSquaredSeamCassiniSource_eq_zero_iff_exists_zeroCopy,
    analyticOrderAt_xiSquaredSeamCassiniSource_cassiniZero_eq_multiplicity,
    xiSquaredSeam_tsum_cassiniZero_eq_two_mul_sourceZeroCopy,
    fun _r hr => xiSquaredSeamCassiniJensenExcess_nonneg hr,
    xiSquaredSeamPowerSixtyFourJensenDivisorIntegral_eq_hermitianMass⟩

/-- Strengthened unconditional source certificate after closing the circle-average and
functional-equation quotient welds. -/
def XiSquaredSeamCassiniGlobalSourceCertificate : Prop :=
  XiSquaredSeamCassiniUniversalSourceCertificate ∧
  xiSquaredSeamCassiniPowerSixtyFourJensenIntegral.toReal =
    xiSquaredSeamPowerSixtyFourHermitianMass / 8192 ∧
  xiSquaredSeamPowerThirtyTwoTransverseCharge =
    4096 * xiSquaredSeamCassiniPowerSixtyFourJensenIntegral.toReal -
      (primeArchShiftedReciprocalMoment 1 63).re / 2

theorem xiSquaredSeamCassiniGlobalSourceCertificate_proof :
    XiSquaredSeamCassiniGlobalSourceCertificate := by
  exact ⟨xiSquaredSeamCassiniUniversalSourceCertificate_proof,
    xiSquaredSeamCassiniPowerSixtyFourJensenIntegral_toReal,
    xiSquaredSeamPowerThirtyTwoTransverseCharge_eq_cassiniJensenResidual⟩

/-- Simultaneous dyadic, all-cutoff Hankel, transverse-charge, and power-64 source realization. -/
def XiSquaredSeamDyadicMomentUniversalCertificate : Prop :=
  XiSquaredSeamDyadicHalfPlane ∧
  XiSquaredSeamDyadicTailFromFive ∧
  XiSquaredSeamDyadicTailFromSix ∧
  XiSquaredSeamPowerThirtyTwoAnnulusEmpty ∧
  (∀ M : ℕ, XiShiftedReciprocalHankelTailNonnegative 1 M) ∧
  (∀ M : ℕ, PrimeArchShiftedReciprocalHankelTailNonnegative 1 M) ∧
  xiSquaredSeamPowerSixtyFourDefectEnergy = 0 ∧
  xiSquaredSeamPowerSixtyFourHermitianMass =
    (primeArchShiftedReciprocalMoment 1 63).re ∧
  XiSquaredSeamPowerSixtyFourSourceDominated

/-- Combined unconditional Cassini-source and orientation certificate. -/
def XiSquaredSeamCassiniDyadicUniversalCertificate : Prop :=
  XiSquaredSeamCassiniUniversalSourceCertificate ∧
  XiSquaredSeamDyadicMomentUniversalCertificate

/-- **Xi squared-seam Cassini--dyadic universality law.** One reverse power-64 source inequality
holds exactly when the unconditional Cassini source and nine dyadic, Hankel, defect, and
power-64 source charts are realized simultaneously. -/
theorem xiSquaredSeamPowerSixtyFourSourceDominated_iff_cassiniDyadicUniversalCertificate :
    XiSquaredSeamPowerSixtyFourSourceDominated ↔
      XiSquaredSeamCassiniDyadicUniversalCertificate := by
  constructor
  · intro hdom
    have hRH : RiemannHypothesis :=
      xiSquaredSeamPowerSixtyFourSourceDominated_iff_riemannHypothesis.1 hdom
    have hdefect : xiSquaredSeamPowerSixtyFourDefectEnergy = 0 :=
      xiSquaredSeamPowerSixtyFourDefectEnergy_eq_zero_of_riemannHypothesis hRH
    have hgap := xiSquaredSeamPowerSixtyFourHermitianMass_sub_source_eq_defect
    rw [hdefect] at hgap
    have hmass : xiSquaredSeamPowerSixtyFourHermitianMass =
        (primeArchShiftedReciprocalMoment 1 63).re := sub_eq_zero.1 hgap
    exact ⟨
      xiSquaredSeamCassiniUniversalSourceCertificate_proof,
      xiSquaredSeamDyadicHalfPlane_iff_riemannHypothesis.2 hRH,
      xiSquaredSeamDyadicTailFromFive_iff_riemannHypothesis.2 hRH,
      xiSquaredSeamDyadicTailFromSix_iff_riemannHypothesis.2 hRH,
      xiSquaredSeamPowerThirtyTwoAnnulusEmpty_of_riemannHypothesis hRH,
      fun M => (xiShiftedReciprocalHankelTailNonnegative_iff_riemannHypothesis
        (y := 1) (by norm_num) M).2 hRH,
      fun M => (primeArchShiftedReciprocalHankelTailNonnegative_one_iff_riemannHypothesis
        M).2 hRH,
      hdefect,
      hmass,
      hdom⟩
  · intro hcertificate
    apply xiSquaredSeamPowerSixtyFourSourceDominated_iff_riemannHypothesis.2
    exact xiSquaredSeamDyadicHalfPlane_iff_riemannHypothesis.1 hcertificate.2.1

/-- Simultaneous strict scalar, dyadic-rung, and every-cutoff shifted-Hankel witnesses. -/
def XiSquaredSeamCassiniDyadicFailureUniversalCertificate : Prop :=
  0 < xiSquaredSeamPowerSixtyFourDefectEnergy ∧
  (primeArchShiftedReciprocalMoment 1 63).re <
    xiSquaredSeamPowerSixtyFourHermitianMass ∧
  (∃ q : XiZeroCopy, ∃ k : ℕ,
    ((xiSquaredSeamOneCoordinate q) ^ (2 ^ k)).re < 0) ∧
  (∃ q : XiZeroCopy, ∃ k : ℕ, 5 ≤ k ∧
    ((xiSquaredSeamOneCoordinate q) ^ (2 ^ k)).re < 0) ∧
  (∃ q : XiZeroCopy, ∃ k : ℕ, 6 ≤ k ∧
    ((xiSquaredSeamOneCoordinate q) ^ (2 ^ k)).re < 0) ∧
  (∀ M : ℕ, ∃ N : ℕ, ∃ c : Fin N → ℝ,
    (∑ i : Fin N, ∑ j : Fin N,
      c i * c j *
        (xiShiftedReciprocalMoment 1
          (2 * M + (i : ℕ) + (j : ℕ))).re) < 0) ∧
  (∀ M : ℕ, ∃ N : ℕ, ∃ c : Fin N → ℝ,
    (∑ i : Fin N, ∑ j : Fin N,
      c i * c j *
        (primeArchShiftedReciprocalMoment 1
          (2 * M + (i : ℕ) + (j : ℕ))).re) < 0)

/-- **Complementary squared-seam Cassini--dyadic failure law.** Failure of RH is equivalent to
positive transverse/triangle defects, strict source mass loss, negative dyadic rungs, and negative
zero-side and source-side Hankel forms after every finite cutoff. -/
theorem not_riemannHypothesis_iff_squaredSeamCassiniDyadicFailureUniversalCertificate :
    ¬RiemannHypothesis ↔
      XiSquaredSeamCassiniDyadicFailureUniversalCertificate := by
  classical
  constructor
  · intro hnotRH
    have hdefectNe : xiSquaredSeamPowerSixtyFourDefectEnergy ≠ 0 := by
      intro hzero
      have hgap := xiSquaredSeamPowerSixtyFourHermitianMass_sub_source_eq_defect
      rw [hzero] at hgap
      have hdom : XiSquaredSeamPowerSixtyFourSourceDominated :=
        (sub_eq_zero.1 hgap).le
      exact hnotRH
        (xiSquaredSeamPowerSixtyFourSourceDominated_iff_riemannHypothesis.1 hdom)
    have hdefectPos : 0 < xiSquaredSeamPowerSixtyFourDefectEnergy :=
      lt_of_le_of_ne xiSquaredSeamPowerSixtyFourDefectEnergy_nonneg hdefectNe.symm
    have hmassLoss : (primeArchShiftedReciprocalMoment 1 63).re <
        xiSquaredSeamPowerSixtyFourHermitianMass := by
      have hgap := xiSquaredSeamPowerSixtyFourHermitianMass_sub_source_eq_defect
      linarith
    have hnotDyadic : ¬XiSquaredSeamDyadicHalfPlane := by
      intro hdyadic
      exact hnotRH (xiSquaredSeamDyadicHalfPlane_iff_riemannHypothesis.1 hdyadic)
    simp only [XiSquaredSeamDyadicHalfPlane,
      GaloisForLFunctions.ComplexDyadicHalfPlane] at hnotDyadic
    push Not at hnotDyadic
    have hnotFive : ¬XiSquaredSeamDyadicTailFromFive := by
      intro htail
      exact hnotRH (xiSquaredSeamDyadicTailFromFive_iff_riemannHypothesis.1 htail)
    rw [XiSquaredSeamDyadicTailFromFive] at hnotFive
    push Not at hnotFive
    have hnotSix : ¬XiSquaredSeamDyadicTailFromSix := by
      intro htail
      exact hnotRH (xiSquaredSeamDyadicTailFromSix_iff_riemannHypothesis.1 htail)
    rw [XiSquaredSeamDyadicTailFromSix] at hnotSix
    push Not at hnotSix
    have hzeroTail : ∀ M : ℕ, ∃ N : ℕ, ∃ c : Fin N → ℝ,
        (∑ i : Fin N, ∑ j : Fin N,
          c i * c j *
            (xiShiftedReciprocalMoment 1
              (2 * M + (i : ℕ) + (j : ℕ))).re) < 0 := by
      intro M
      have hnot : ¬XiShiftedReciprocalHankelTailNonnegative 1 M := by
        intro htail
        exact hnotRH
          ((xiShiftedReciprocalHankelTailNonnegative_iff_riemannHypothesis
            (y := 1) (by norm_num) M).1 htail)
      rw [XiShiftedReciprocalHankelTailNonnegative] at hnot
      push Not at hnot
      exact hnot
    have hsourceTail : ∀ M : ℕ, ∃ N : ℕ, ∃ c : Fin N → ℝ,
        (∑ i : Fin N, ∑ j : Fin N,
          c i * c j *
            (primeArchShiftedReciprocalMoment 1
              (2 * M + (i : ℕ) + (j : ℕ))).re) < 0 := by
      intro M
      have hnot : ¬PrimeArchShiftedReciprocalHankelTailNonnegative 1 M := by
        intro htail
        exact hnotRH
          ((primeArchShiftedReciprocalHankelTailNonnegative_one_iff_riemannHypothesis
            M).1 htail)
      rw [PrimeArchShiftedReciprocalHankelTailNonnegative] at hnot
      push Not at hnot
      exact hnot
    exact ⟨hdefectPos, hmassLoss, hnotDyadic, hnotFive, hnotSix,
      hzeroTail, hsourceTail⟩
  · intro hcertificate hRH
    have hzero :=
      xiSquaredSeamPowerSixtyFourDefectEnergy_eq_zero_of_riemannHypothesis hRH
    exact (ne_of_gt hcertificate.1) hzero

end

end RHTower
