import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureHeightLocalFrame
import GaloisForLFunctions.RHTower.HedenmalmThetaAnomalyWardKreinPythagoreanDefect

/-!
# Ward-defect transverse Green source

The inverse-square factor in the height-local five-shift current is not inserted as an external
spectral coefficient.  The positive Euclidean energy hidden by same-fibre Ward cancellation is
exactly twice transverse displacement squared times genuine Ward mass squared.  Dividing twice
mass squared by that source-derived defect therefore produces the required transverse Green
weight, with the critical-line kernel retained by the totalized inverse.

The resulting Ward--Green current is definitionally source-normalized and exactly equals the
P-G148 singular critical-feature current.  Hence every strict-right Xi copy keeps its universal
nearest-integer charge.  This realizes the singular factor and classifies its kernel; it does not
prove the remaining arithmetic trace ceiling.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Positive Ward defect and its Green inverse -/

/-- The Ward Euclidean defect is exactly transverse displacement squared times twice genuine
Ward mass squared. -/
theorem thetaXiWardEuclideanEnergy_eq_transverse_sq_mul_mass_sq
    (q : XiZeroCopy) :
    thetaXiWardEuclideanEnergy q =
      2 * (xiSpectralPoint q).im ^ (2 : ℕ) *
        thetaXiWardRealificationMass q ^ (2 : ℕ) := by
  rw [thetaXiWardEuclideanEnergy_eq_two_mul_anomaly_normSq,
    thetaXiWardRealificationAnomaly_eq]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Source-defined transverse Green weight: inverse Ward defect normalized by genuine Ward mass.
No spectral coordinate occurs in the definition. -/
def thetaXiWardTransverseGreenWeight (q : XiZeroCopy) : ℝ :=
  2 * thetaXiWardRealificationMass q ^ (2 : ℕ) /
    thetaXiWardEuclideanEnergy q

/-- **Exact source Green identity.**  The Ward-defect inverse is the forced inverse-square
transverse weight, including the totalized zero on the critical-line kernel. -/
theorem thetaXiWardTransverseGreenWeight_eq
    (q : XiZeroCopy) :
    thetaXiWardTransverseGreenWeight q =
      ((xiSpectralPoint q).im)⁻¹ ^ (2 : ℕ) := by
  rw [thetaXiWardTransverseGreenWeight,
    thetaXiWardEuclideanEnergy_eq_transverse_sq_mul_mass_sq]
  by_cases him : (xiSpectralPoint q).im = 0
  · simp [him]
  · have hmass : thetaXiWardRealificationMass q ≠ 0 :=
      (thetaXiWardRealificationMass_pos q).ne'
    field_simp

/-- The source Green weight has exactly the critical-line kernel. -/
theorem thetaXiWardTransverseGreenWeight_eq_zero_iff
    (q : XiZeroCopy) :
    thetaXiWardTransverseGreenWeight q = 0 ↔
      (xiSpectralPoint q).im = 0 := by
  rw [thetaXiWardTransverseGreenWeight_eq]
  constructor
  · intro h
    by_contra him
    exact (pow_ne_zero 2 (inv_ne_zero him)) h
  · intro him
    simp [him]

/-- Away from its kernel, the Green weight is strictly positive. -/
theorem thetaXiWardTransverseGreenWeight_pos_of_im_ne_zero
    (q : XiZeroCopy) (him : (xiSpectralPoint q).im ≠ 0) :
    0 < thetaXiWardTransverseGreenWeight q := by
  rw [thetaXiWardTransverseGreenWeight_eq]
  exact sq_pos_of_ne_zero (inv_ne_zero him)

/-- The unbounded inverse-graph law.  It is asserted only off the Ward kernel; on the critical
line the totalized Green weight is zero while genuine Ward mass remains positive. -/
theorem thetaXiWardTransverseGreenWeight_mul_euclideanEnergy
    (q : XiZeroCopy) (him : (xiSpectralPoint q).im ≠ 0) :
    thetaXiWardTransverseGreenWeight q * thetaXiWardEuclideanEnergy q =
      2 * thetaXiWardRealificationMass q ^ (2 : ℕ) := by
  rw [thetaXiWardTransverseGreenWeight_eq,
    thetaXiWardEuclideanEnergy_eq_transverse_sq_mul_mass_sq]
  field_simp

/-! ## Exact singular critical-feature landing -/

/-- Functional-equation-paired five-shift feature current normalized by the source Ward Green
weight rather than an inserted spectral inverse square. -/
def fiveShiftCriticalFeatureWardGreenCurrent
    (t : ℝ) (q : XiZeroCopy) : ℝ :=
  let z := xiSpectralPoint q
  let hz := abs_xiSpectralPoint_im_lt_half q
  let hzc : |((starRingEnd ℂ) z).im| < 1 / 2 := by simpa using hz
  thetaXiWardTransverseGreenWeight q *
    (-(fiveShiftCriticalEvaluationEnergyCurrent 1 (by norm_num) z hz
          (HedenmalmThetaSource.criticalFeature (t : ℂ) (by norm_num)) +
        fiveShiftCriticalEvaluationEnergyCurrent 1 (by norm_num)
          ((starRingEnd ℂ) z) hzc
          (HedenmalmThetaSource.criticalFeature (t : ℂ) (by norm_num))))

/-- Source Ward--Green normalization reproduces P-G148's singular current exactly. -/
theorem fiveShiftCriticalFeatureWardGreenCurrent_eq
    (t : ℝ) (q : XiZeroCopy) :
    fiveShiftCriticalFeatureWardGreenCurrent t q =
      fiveShiftCriticalFeaturePairedRenormalizedCurrent t
        (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q) := by
  rw [fiveShiftCriticalFeatureWardGreenCurrent,
    fiveShiftCriticalFeaturePairedRenormalizedCurrent,
    thetaXiWardTransverseGreenWeight_eq]
  simp only [inv_neg, neg_sq]

/-- Every strict-right Xi copy retains the universal nearest-integer five-shift charge after the
inverse-square factor is realized entirely by the Ward-defect Green graph. -/
theorem fiveShiftCriticalFeatureWardGreenCurrent_xiRightZeroCopy_round_ge
    (q : XiRightZeroCopy) :
    (64 / 2025 : ℝ) ≤
      fiveShiftCriticalFeatureWardGreenCurrent
        ((round (xiSpectralPoint q.1).re : ℤ) : ℝ) q.1 := by
  rw [fiveShiftCriticalFeatureWardGreenCurrent_eq]
  exact
    fiveShiftCriticalFeaturePairedRenormalizedCurrent_xiRightZeroCopy_round_ge q

end

end RHTower
