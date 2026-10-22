import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaCompactDivisorEigenmode
import GaloisForLFunctions.RHTower.XiShiftedReciprocalHankelTailCriterion

/-!
# The squared-Xi seam as a theta compact-operator pencil

Every multiplicity-exact Xi zero is already a genuine nonzero eigenvector of the fixed compact
theta source inverse.  Squaring that eigen-equation and applying the shift-one Möbius transform
identifies the squared-seam coordinate with the unique generalized eigenvalue of the pencil
`(B², I + B²)` on the corresponding divisor line.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

open HedenmalmQuantile HedenmalmThetaSource

/-- Every multiplicity copy of the centered Xi divisor lies in the natural theta-source strip. -/
theorem thetaXiSpectralPoint_mem_sourceStrip (q : XiZeroCopy) :
    |(xiSpectralPoint q).im| < 1 := by
  rw [abs_lt]
  constructor <;> linarith [xiSpectralPoint_im_mem_openHalf q]

/-- The actual Xi divisor is the divisor of the theta source transform. -/
theorem xiC_thetaSource_xiSpectralPoint_eq_zero (q : XiZeroCopy) :
    xiC thetaSource (xiSpectralPoint q) = 0 := by
  rw [xiC_thetaSource (thetaXiSpectralPoint_mem_sourceStrip q)]
  exact XiC_xiSpectralPoint_eq_zero q

/-- Canonical quantile-space theta eigenvector attached to one multiplicity copy. -/
def thetaXiDivisorEigenvector (q : XiZeroCopy) :
    Lp ℂ 2 unitIntervalMeasure :=
  thetaDivisorEigenvector (xiSpectralPoint q)
    (thetaXiSpectralPoint_mem_sourceStrip q)
    (xiC_thetaSource_xiSpectralPoint_eq_zero q)

/-- Reciprocal eigenvalue of the compact theta source inverse. -/
def thetaXiReciprocalEigenvalue (q : XiZeroCopy) : ℂ :=
  -(xiSpectralPoint q)⁻¹

theorem thetaXiDivisorEigenvector_ne_zero (q : XiZeroCopy) :
    thetaXiDivisorEigenvector q ≠ 0 := by
  exact thetaDivisorEigenvector_ne_zero (xiSpectralPoint q)
    (thetaXiSpectralPoint_mem_sourceStrip q)
    (xiC_thetaSource_xiSpectralPoint_eq_zero q)

/-- Each actual Xi copy is a genuine eigenmode of one fixed source-built compact operator. -/
theorem thetaCompactSourceInverse_thetaXi_eigen (q : XiZeroCopy) :
    thetaCompactSourceInverse (thetaXiDivisorEigenvector q) =
      thetaXiReciprocalEigenvalue q • thetaXiDivisorEigenvector q := by
  exact thetaCompactSourceInverse_eigen (xiSpectralPoint q)
    (thetaXiSpectralPoint_mem_sourceStrip q)
    (xiC_thetaSource_xiSpectralPoint_eq_zero q)

/-- Squaring the compact source inverse squares its reciprocal Xi eigenvalue. -/
theorem thetaCompactSourceInverse_sq_thetaXi_eigen (q : XiZeroCopy) :
    thetaCompactSourceInverse
        (thetaCompactSourceInverse (thetaXiDivisorEigenvector q)) =
      thetaXiReciprocalEigenvalue q ^ (2 : ℕ) • thetaXiDivisorEigenvector q := by
  rw [thetaCompactSourceInverse_thetaXi_eigen, map_smul,
    thetaCompactSourceInverse_thetaXi_eigen, smul_smul]
  simp only [pow_two]

/-- The squared reciprocal eigenvalue is exactly the unshifted reciprocal-square Xi atom. -/
theorem thetaXiReciprocalEigenvalue_sq_eq_reciprocalSquare (q : XiZeroCopy) :
    thetaXiReciprocalEigenvalue q ^ (2 : ℕ) = xiZeroCopyReciprocalSquare q := by
  simp only [thetaXiReciprocalEigenvalue, xiZeroCopyReciprocalSquare]
  ring

/-- The squared-seam atom is the shift-one rational transform of the theta eigenvalue square. -/
theorem xiSquaredSeamOneCoordinate_eq_thetaXi_pencilRatio (q : XiZeroCopy) :
    xiSquaredSeamOneCoordinate q =
      thetaXiReciprocalEigenvalue q ^ (2 : ℕ) /
        (1 + thetaXiReciprocalEigenvalue q ^ (2 : ℕ)) := by
  rw [← xiShiftedReciprocalSquare_one_eq_xiSquaredSeamOneCoordinate,
    xiShiftedReciprocalSquare, thetaXiReciprocalEigenvalue_sq_eq_reciprocalSquare]
  simp only [Complex.ofReal_one, one_mul]

theorem one_add_thetaXiReciprocalEigenvalue_sq_ne_zero (q : XiZeroCopy) :
    1 + thetaXiReciprocalEigenvalue q ^ (2 : ℕ) ≠ 0 := by
  rw [thetaXiReciprocalEigenvalue_sq_eq_reciprocalSquare]
  simpa using one_add_mul_xiZeroCopyReciprocalSquare_ne_zero
    (y := 1) (by norm_num) q

/-- The right-hand vector of the squared theta pencil never degenerates. -/
theorem thetaXiDivisorEigenvector_add_sq_ne_zero (q : XiZeroCopy) :
    thetaXiDivisorEigenvector q +
        thetaCompactSourceInverse
      (thetaCompactSourceInverse (thetaXiDivisorEigenvector q)) ≠ 0 := by
  rw [thetaCompactSourceInverse_sq_thetaXi_eigen]
  have hsum : thetaXiDivisorEigenvector q +
      thetaXiReciprocalEigenvalue q ^ (2 : ℕ) • thetaXiDivisorEigenvector q =
        (1 + thetaXiReciprocalEigenvalue q ^ (2 : ℕ)) • thetaXiDivisorEigenvector q := by
    rw [add_smul, one_smul]
  rw [hsum]
  exact smul_ne_zero (one_add_thetaXiReciprocalEigenvalue_sq_ne_zero q)
    (thetaXiDivisorEigenvector_ne_zero q)

/-- **Frankenstein join.** The squared-seam coordinate is a generalized eigenvalue of the
source-built compact pencil `(B², I + B²)` on its genuine Xi divisor mode. -/
theorem thetaCompactSourceInverse_sq_pencil (q : XiZeroCopy) :
    thetaCompactSourceInverse
        (thetaCompactSourceInverse (thetaXiDivisorEigenvector q)) =
      xiSquaredSeamOneCoordinate q •
        (thetaXiDivisorEigenvector q +
          thetaCompactSourceInverse
            (thetaCompactSourceInverse (thetaXiDivisorEigenvector q))) := by
  rw [thetaCompactSourceInverse_sq_thetaXi_eigen]
  have hsum : thetaXiDivisorEigenvector q +
      thetaXiReciprocalEigenvalue q ^ (2 : ℕ) • thetaXiDivisorEigenvector q =
        (1 + thetaXiReciprocalEigenvalue q ^ (2 : ℕ)) • thetaXiDivisorEigenvector q := by
    rw [add_smul, one_smul]
  rw [hsum, smul_smul,
    xiSquaredSeamOneCoordinate_eq_thetaXi_pencilRatio]
  congr 1
  field_simp [one_add_thetaXiReciprocalEigenvalue_sq_ne_zero q]

/-- The pencil eigenvalue is unique on each nonzero theta divisor line. -/
theorem thetaCompactSourceInverse_sq_pencil_unique (q : XiZeroCopy) {mu : ℂ}
    (hmu :
      thetaCompactSourceInverse
          (thetaCompactSourceInverse (thetaXiDivisorEigenvector q)) =
        mu •
          (thetaXiDivisorEigenvector q +
            thetaCompactSourceInverse
              (thetaCompactSourceInverse (thetaXiDivisorEigenvector q)))) :
    mu = xiSquaredSeamOneCoordinate q := by
  have hcanonical := thetaCompactSourceInverse_sq_pencil q
  have hsmul : mu •
        (thetaXiDivisorEigenvector q +
          thetaCompactSourceInverse
            (thetaCompactSourceInverse (thetaXiDivisorEigenvector q))) =
      xiSquaredSeamOneCoordinate q •
        (thetaXiDivisorEigenvector q +
          thetaCompactSourceInverse
            (thetaCompactSourceInverse (thetaXiDivisorEigenvector q))) :=
    hmu.symm.trans hcanonical
  exact smul_left_injective ℂ
    (thetaXiDivisorEigenvector_add_sq_ne_zero q) hsmul

end

end RHTower
