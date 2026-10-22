import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilPrimeEntryIncidence
import GaloisForLFunctions.RHTower.CCM.CCMRawStieltjesChamberIndexInflation

/-!
# Rank-one whole-matrix tangent at a prime-entry wall

The single-atom four-unit law has a stronger whole-packet consequence.  Its odd-source tangent is
linear in centered clock, while its diagonal tangent is the same constant at every mode.  The
divided difference therefore turns every off-diagonal tangent into that identical constant.

This file proves entrywise that the derivative of the entire centered event packet is a scalar
multiple of the outer product of the constant CCM boundary vector with itself.  Thus every entering
prime atom activates one canonical rank-one boundary incidence direction before quotient loss.
-/

noncomputable section

open scoped BigOperators Interval

namespace RHTower

open Matrix MeasureTheory Set Filter Topology

/-- Common matrix-entry rate contributed by index `k` at its aperture wall. -/
def ccmGuinandWeilPrimeEntryMatrixRate (k : ℕ) : ℝ :=
  -4 * criticalMellinAtomWeight k / Real.log k

/-- Single-atom odd germ on a finite centered packet. -/
def ccmGuinandWeilPrimeEntryCenteredSource
    (k : ℕ) (N : ℕ) (a : ℝ) (i : Fin (2 * N + 1)) : ℝ :=
  ccmGuinandWeilPrimeEntryOddGerm k (ccmPublishedCenteredMode N i) a

/-- Single-atom diagonal germ on a finite centered packet. -/
def ccmGuinandWeilPrimeEntryCenteredDiagonal
    (k : ℕ) (N : ℕ) (a : ℝ) (i : Fin (2 * N + 1)) : ℝ :=
  ccmGuinandWeilPrimeEntryDiagonalGerm k (ccmPublishedCenteredMode N i) a

/-- Whole centered divided-difference packet of one entering atom. -/
def ccmGuinandWeilPrimeEntryCenteredMatrix
    (k : ℕ) (N : ℕ) (a : ℝ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  ccmDividedDifferenceMatrix
    (ccmPublishedCenteredClock N)
    (ccmGuinandWeilPrimeEntryCenteredSource k N a)
    (ccmGuinandWeilPrimeEntryCenteredDiagonal k N a)

/-- Canonical rank-one whole-packet tangent attached to index `k`. -/
def ccmGuinandWeilPrimeEntryRankOneTangent (k : ℕ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  ccmGuinandWeilPrimeEntryMatrixRate k •
    Matrix.vecMulVec
      (ccmConstantBoundary : Fin (2 * N + 1) → ℝ)
      ccmConstantBoundary

/-- Centered odd-source tangent is clock times the common entry rate. -/
theorem hasDerivAt_ccmGuinandWeilPrimeEntryCenteredSource_entry
    {k : ℕ} (hk : 1 < k) (N : ℕ) (i : Fin (2 * N + 1)) :
    HasDerivAt (fun a => ccmGuinandWeilPrimeEntryCenteredSource k N a i)
      (ccmPublishedCenteredClock N i * ccmGuinandWeilPrimeEntryMatrixRate k)
      (ccmGuinandWeilPrimeEntryAperture k) := by
  have h := hasDerivAt_ccmGuinandWeilPrimeEntryOddGerm_entry hk
    (ccmPublishedCenteredMode N i)
  apply h.congr_deriv
  rw [ccmGuinandWeilPrimeEntryMatrixRate, ccmPublishedCenteredClock]
  ring

/-- Every centered diagonal tangent equals the common entry rate. -/
theorem hasDerivAt_ccmGuinandWeilPrimeEntryCenteredDiagonal_entry
    {k : ℕ} (hk : 1 < k) (N : ℕ) (i : Fin (2 * N + 1)) :
    HasDerivAt (fun a => ccmGuinandWeilPrimeEntryCenteredDiagonal k N a i)
      (ccmGuinandWeilPrimeEntryMatrixRate k)
      (ccmGuinandWeilPrimeEntryAperture k) := by
  exact hasDerivAt_ccmGuinandWeilPrimeEntryDiagonalGerm_entry hk
    (ccmPublishedCenteredMode N i)

/-- Diagonal and divided-difference cases have the same aperture derivative at entry. -/
theorem hasDerivAt_ccmGuinandWeilPrimeEntryCenteredMatrix_apply_entry
    {k : ℕ} (hk : 1 < k) (N : ℕ)
    (i j : Fin (2 * N + 1)) :
    HasDerivAt (fun a => ccmGuinandWeilPrimeEntryCenteredMatrix k N a i j)
      (ccmGuinandWeilPrimeEntryMatrixRate k)
      (ccmGuinandWeilPrimeEntryAperture k) := by
  by_cases hij : i = j
  · subst j
    simpa [ccmGuinandWeilPrimeEntryCenteredMatrix, ccmDividedDifferenceMatrix] using
      hasDerivAt_ccmGuinandWeilPrimeEntryCenteredDiagonal_entry hk N i
  · have hi := hasDerivAt_ccmGuinandWeilPrimeEntryCenteredSource_entry hk N i
    have hj := hasDerivAt_ccmGuinandWeilPrimeEntryCenteredSource_entry hk N j
    have hnumer := hi.sub hj
    have hclock : ccmPublishedCenteredClock N i -
        ccmPublishedCenteredClock N j ≠ 0 :=
      sub_ne_zero.mpr ((ccmPublishedCenteredClock_injective N).ne hij)
    have hquot := hnumer.div_const
      (ccmPublishedCenteredClock N i - ccmPublishedCenteredClock N j)
    have hquot' : HasDerivAt
        (fun a =>
          (ccmGuinandWeilPrimeEntryCenteredSource k N a i -
              ccmGuinandWeilPrimeEntryCenteredSource k N a j) /
            (ccmPublishedCenteredClock N i - ccmPublishedCenteredClock N j))
        (ccmGuinandWeilPrimeEntryMatrixRate k)
        (ccmGuinandWeilPrimeEntryAperture k) :=
      hquot.congr_deriv (by field_simp [hclock])
    simpa [ccmGuinandWeilPrimeEntryCenteredMatrix, ccmDividedDifferenceMatrix, hij] using hquot'

/-- **Rank-one whole-matrix event law.** Entrywise aperture derivative is the common rate times
the outer product of the two constant CCM boundary vectors. -/
theorem ccmGuinandWeilPrimeEntryCenteredMatrix_deriv_eq_rankOne
    {k : ℕ} (hk : 1 < k) (N : ℕ) :
    (fun i j =>
      deriv (fun a => ccmGuinandWeilPrimeEntryCenteredMatrix k N a i j)
        (ccmGuinandWeilPrimeEntryAperture k)) =
      ccmGuinandWeilPrimeEntryRankOneTangent k N := by
  ext i j
  rw [(hasDerivAt_ccmGuinandWeilPrimeEntryCenteredMatrix_apply_entry hk N i j).deriv]
  simp [ccmGuinandWeilPrimeEntryRankOneTangent,
    Matrix.vecMulVec_apply, ccmConstantBoundary]

/-- Genuine prime-power entry events have strictly negative matrix rate. -/
theorem ccmGuinandWeilPrimeEntryMatrixRate_neg
    {k : ℕ} (hk : IsPrimePow k) :
    ccmGuinandWeilPrimeEntryMatrixRate k < 0 := by
  rw [ccmGuinandWeilPrimeEntryMatrixRate]
  have hw := criticalMellinAtomWeight_pos hk
  have hlog : 0 < Real.log k := Real.log_pos (by exact_mod_cast hk.one_lt)
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hw) hlog

/-- Exact quadratic form of the atomic rank-one tangent. -/
theorem ccmGuinandWeilPrimeEntryRankOneTangent_quadratic
    (k : ℕ) (N : ℕ) (v : Fin (2 * N + 1) → ℝ) :
    dotProduct v (ccmGuinandWeilPrimeEntryRankOneTangent k N *ᵥ v) =
      ccmGuinandWeilPrimeEntryMatrixRate k * (∑ i, v i) ^ (2 : ℕ) := by
  simp only [ccmGuinandWeilPrimeEntryRankOneTangent, dotProduct, Matrix.mulVec,
    Matrix.smul_apply, Matrix.vecMulVec_apply, ccmConstantBoundary,
    smul_eq_mul, one_mul]
  rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  ring

/-- Every genuine prime-power event tangent is negative semidefinite. -/
theorem ccmGuinandWeilPrimeEntryRankOneTangent_quadratic_nonpos
    {k : ℕ} (hk : IsPrimePow k) (N : ℕ)
    (v : Fin (2 * N + 1) → ℝ) :
    dotProduct v (ccmGuinandWeilPrimeEntryRankOneTangent k N *ᵥ v) ≤ 0 := by
  rw [ccmGuinandWeilPrimeEntryRankOneTangent_quadratic]
  exact mul_nonpos_of_nonpos_of_nonneg
    (ccmGuinandWeilPrimeEntryMatrixRate_neg hk).le (sq_nonneg _)

/-- The atomic whole-packet tangent has matrix rank at most one. -/
theorem ccmGuinandWeilPrimeEntryRankOneTangent_rank_le_one
    (k : ℕ) (N : ℕ) :
    (ccmGuinandWeilPrimeEntryRankOneTangent k N).rank ≤ 1 := by
  have heq : ccmGuinandWeilPrimeEntryRankOneTangent k N =
      Matrix.vecMulVec
        (ccmGuinandWeilPrimeEntryMatrixRate k •
          (ccmConstantBoundary : Fin (2 * N + 1) → ℝ))
        ccmConstantBoundary := by
    ext i j
    simp [ccmGuinandWeilPrimeEntryRankOneTangent,
      Matrix.vecMulVec_apply, ccmConstantBoundary]
  rw [heq]
  exact Matrix.rank_vecMulVec_le _ _

end RHTower
