import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarParabolicSourceBoundary
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarRelativeDisplacement

/-!
# Orientation--debt factorization of the literal parabolic cross current

The strict cross-cell current is the exact source quantity retained by the SP-E parabolic
carrier.  Its sign is not cellwise: displacement increments can be either overlaps or gaps.

This module removes a separate geometric ambiguity.  The literal matched-cell barycentres are
strictly ordered, unconditionally.  Consequently every cross kernel is exactly a signed
displacement-orientation ledger, with a nonnegative geometric coefficient, minus a nonnegative
quadratic debt.  At adjacent indices the signed ledger is precisely the literal oriented
matched-cell gap.  Thus the only sign-bearing source channel is an all-scale aggregation of those
oriented gaps; neither a local positivity assertion nor a discarded squared debt can replace it.

No bound, sign, or RH implication is asserted.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Arithmetic barycentre of a literal matched polar cell in mass coordinate. -/
def ccmActualHeadMatchedPolarCentroid (n : ℕ) : ℝ :=
  (ccmActualHeadMatchedPolarLowerCoordinate n +
    ccmActualHeadMatchedPolarUpperCoordinate n) / 2

/-- Exact scalar cross kernel of two literal matched--quantile parabolic cells. -/
def ccmActualHeadMatchedQuantileParabolicCrossKernelValue (m n : ℕ) : ℝ :=
  ccmParabolicPairing (ccmActualHeadMatchedParabolicMoment m)
      (ccmActualHeadMatchedParabolicMoment n) -
    ccmParabolicPairing (ccmActualHeadQuantileParabolicMoment m)
      (ccmActualHeadQuantileParabolicMoment n)

/-- Nonnegative geometric coefficient carried by a forward ordered pair of matched cells. -/
def ccmActualHeadMatchedQuantileParabolicOrientationCoefficient (m n : ℕ) : ℝ :=
  criticalMellinAtomWeight m * criticalMellinAtomWeight n *
    (ccmActualHeadMatchedPolarCentroid n - ccmActualHeadMatchedPolarCentroid m)

/-- The only sign-bearing part of a literal parabolic cross kernel. -/
def ccmActualHeadMatchedQuantileParabolicOrientationLedger (m n : ℕ) : ℝ :=
  (ccmActualHeadMatchedQuantilePolarDisplacement n -
      ccmActualHeadMatchedQuantilePolarDisplacement m) *
    ccmActualHeadMatchedQuantileParabolicOrientationCoefficient m n

/-- Forced nonnegative squared displacement debt of one literal parabolic cross kernel. -/
def ccmActualHeadMatchedQuantileParabolicDisplacementDebt (m n : ℕ) : ℝ :=
  (ccmActualHeadMatchedQuantilePolarDisplacement n -
      ccmActualHeadMatchedQuantilePolarDisplacement m) ^ (2 : ℕ) / 2 *
    (criticalMellinAtomWeight m * criticalMellinAtomWeight n)

/-- The matched-cell barycentre is determined exactly by the arithmetic node and the atom width. -/
theorem ccmActualHeadMatchedPolarCentroid_sq (n : ℕ) (hn : 0 < n) :
    ccmActualHeadMatchedPolarCentroid n ^ (2 : ℕ) =
      4 * (n : ℝ) + criticalMellinAtomWeight n ^ (2 : ℕ) / 4 := by
  have hprod := ccmActualHeadMatchedPolarLower_mul_upper n hn
  have hwidth := ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight n
  unfold ccmActualHeadMatchedPolarCentroid
  calc
    ((ccmActualHeadMatchedPolarLowerCoordinate n +
        ccmActualHeadMatchedPolarUpperCoordinate n) / 2) ^ (2 : ℕ) =
        ccmActualHeadMatchedPolarLowerCoordinate n *
          ccmActualHeadMatchedPolarUpperCoordinate n +
        (ccmActualHeadMatchedPolarUpperCoordinate n -
          ccmActualHeadMatchedPolarLowerCoordinate n) ^ (2 : ℕ) / 4 := by ring
    _ = _ := by rw [hprod, hwidth]

theorem ccmActualHeadMatchedPolarCentroid_pos (n : ℕ) :
    0 < ccmActualHeadMatchedPolarCentroid n := by
  unfold ccmActualHeadMatchedPolarCentroid ccmActualHeadMatchedPolarLowerCoordinate
    ccmActualHeadMatchedPolarUpperCoordinate
  positivity

/-- **Source geometry order law.**  Every live matched-cell barycentre is strictly ordered by
its arithmetic index.  The proof uses the exact product-width identity and the unconditional
atom-width ceiling; it does not assume any prime-gap estimate. -/
theorem strictMono_ccmActualHeadMatchedPolarCentroid_shift_two :
    StrictMono (fun n : ℕ => ccmActualHeadMatchedPolarCentroid (n + 2)) := by
  intro m n hmn
  have hmpos : 0 < m + 2 := by omega
  have hnpos : 0 < n + 2 := by omega
  have hmsq := ccmActualHeadMatchedPolarCentroid_sq (m + 2) hmpos
  have hnsq := ccmActualHeadMatchedPolarCentroid_sq (n + 2) hnpos
  norm_num [Nat.cast_add] at hmsq hnsq
  have hwm0 : 0 ≤ criticalMellinAtomWeight (m + 2) :=
    criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _
  have hwn0 : 0 ≤ criticalMellinAtomWeight (n + 2) :=
    criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _
  have hwm2 : criticalMellinAtomWeight (m + 2) ≤ 2 :=
    criticalMellinAtomWeight_le_two_of_pos hmpos
  have hmcenter : 0 < ccmActualHeadMatchedPolarCentroid (m + 2) :=
    ccmActualHeadMatchedPolarCentroid_pos _
  have hncenter : 0 < ccmActualHeadMatchedPolarCentroid (n + 2) :=
    ccmActualHeadMatchedPolarCentroid_pos _
  have hsucc : m + 1 ≤ n := Nat.succ_le_iff.mpr hmn
  have hcast_succ : (m : ℝ) + 1 ≤ n := by exact_mod_cast hsucc
  have hsq_lt : ccmActualHeadMatchedPolarCentroid (m + 2) ^ (2 : ℕ) <
      ccmActualHeadMatchedPolarCentroid (n + 2) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (criticalMellinAtomWeight (m + 2)),
      sq_nonneg (criticalMellinAtomWeight (n + 2))]
  nlinarith

theorem ccmActualHeadMatchedParabolicMoment_one_eq_weight_mul_centroid (n : ℕ) :
    ccmActualHeadMatchedParabolicMoment n 1 =
      criticalMellinAtomWeight n * ccmActualHeadMatchedPolarCentroid n := by
  change (ccmActualHeadMatchedPolarUpperCoordinate n ^ (2 : ℕ) -
      ccmActualHeadMatchedPolarLowerCoordinate n ^ (2 : ℕ)) / 2 =
    criticalMellinAtomWeight n *
      ((ccmActualHeadMatchedPolarLowerCoordinate n +
        ccmActualHeadMatchedPolarUpperCoordinate n) / 2)
  rw [← ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight]
  ring

/-- Every literal parabolic cross kernel is exactly its signed orientation ledger minus its
forced quadratic displacement debt. -/
theorem ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_orientation_sub_debt
    (m n : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCrossKernelValue m n =
      -ccmActualHeadMatchedQuantileParabolicOrientationLedger m n -
        ccmActualHeadMatchedQuantileParabolicDisplacementDebt m n := by
  unfold ccmActualHeadMatchedQuantileParabolicCrossKernelValue
    ccmActualHeadMatchedQuantileParabolicOrientationLedger
    ccmActualHeadMatchedQuantileParabolicDisplacementDebt
  rw [ccmActualHeadMatchedQuantileParabolicCrossKernel,
    ccmActualHeadMatchedParabolicMoment_zero,
    ccmActualHeadMatchedParabolicMoment_zero,
    ccmActualHeadMatchedParabolicMoment_one_eq_weight_mul_centroid,
    ccmActualHeadMatchedParabolicMoment_one_eq_weight_mul_centroid]
  unfold ccmActualHeadMatchedQuantileParabolicOrientationCoefficient
  ring

theorem ccmActualHeadMatchedQuantileParabolicDisplacementDebt_nonneg (m n : ℕ) :
    0 ≤ ccmActualHeadMatchedQuantileParabolicDisplacementDebt m n := by
  unfold ccmActualHeadMatchedQuantileParabolicDisplacementDebt
  exact mul_nonneg
    (div_nonneg (sq_nonneg _) (by norm_num))
    (mul_nonneg (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _) (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _))

/-- After adding the sole signed orientation ledger, every two-cell source current is
unconditionally dissipative. -/
theorem ccmActualHeadMatchedQuantileParabolicCrossKernelValue_add_orientation_nonpos
    (m n : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCrossKernelValue m n +
      ccmActualHeadMatchedQuantileParabolicOrientationLedger m n ≤ 0 := by
  rw [ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_orientation_sub_debt]
  linarith [ccmActualHeadMatchedQuantileParabolicDisplacementDebt_nonneg m n]

/-- Forward matched-cell geometry contributes a nonnegative orientation coefficient.  Thus all
indefiniteness in a forward cross kernel comes from the signed displacement increment itself. -/
theorem ccmActualHeadMatchedQuantileParabolicOrientationCoefficient_nonneg_of_lt
    {m n : ℕ} (hmn : m < n) :
    0 ≤ ccmActualHeadMatchedQuantileParabolicOrientationCoefficient (m + 2) (n + 2) := by
  unfold ccmActualHeadMatchedQuantileParabolicOrientationCoefficient
  exact mul_nonneg
    (mul_nonneg (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _) (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _))
    (sub_nonneg.mpr (strictMono_ccmActualHeadMatchedPolarCentroid_shift_two hmn).le)

/-- Adjacent orientation is exactly the literal signed matched-cell overlap/gap times its
nonnegative geometric coefficient. -/
theorem ccmActualHeadMatchedQuantileParabolicOrientationLedger_succ_eq_adjacentGap
    (n : ℕ) :
    ccmActualHeadMatchedQuantileParabolicOrientationLedger (n + 2) (n + 3) =
      (ccmActualHeadMatchedPolarUpperCoordinate (n + 2) -
        ccmActualHeadMatchedPolarLowerCoordinate (n + 3)) *
      ccmActualHeadMatchedQuantileParabolicOrientationCoefficient (n + 2) (n + 3) := by
  unfold ccmActualHeadMatchedQuantileParabolicOrientationLedger
  have hgap := ccmActualHeadMatchedQuantilePolarDisplacement_succ_sub_eq_adjacentGap (n + 2)
  norm_num [Nat.add_assoc] at hgap
  change (ccmActualHeadMatchedQuantilePolarDisplacement (n + 3) -
      ccmActualHeadMatchedQuantilePolarDisplacement (n + 2)) *
        ccmActualHeadMatchedQuantileParabolicOrientationCoefficient (n + 2) (n + 3) =
      (ccmActualHeadMatchedPolarUpperCoordinate (n + 2) -
        ccmActualHeadMatchedPolarLowerCoordinate (n + 3)) *
        ccmActualHeadMatchedQuantileParabolicOrientationCoefficient (n + 2) (n + 3)
  rw [hgap]

/-- Adjacent cross current: exact signed overlap/gap orientation, minus the full quadratic
displacement debt.  This is a literal identity, not a local sign assertion. -/
theorem ccmActualHeadMatchedQuantileParabolicCrossKernelValue_succ_eq_adjacentGapOrientation_sub_debt
    (n : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCrossKernelValue (n + 2) (n + 3) =
      -(ccmActualHeadMatchedPolarUpperCoordinate (n + 2) -
        ccmActualHeadMatchedPolarLowerCoordinate (n + 3)) *
        ccmActualHeadMatchedQuantileParabolicOrientationCoefficient (n + 2) (n + 3) -
      ccmActualHeadMatchedQuantileParabolicDisplacementDebt (n + 2) (n + 3) := by
  rw [ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_orientation_sub_debt,
    ccmActualHeadMatchedQuantileParabolicOrientationLedger_succ_eq_adjacentGap]
  ring

/-- Ordered all-pair orientation ledger of the finite literal source head. -/
def ccmActualHeadMatchedQuantileParabolicOrientationLedgerSum (K : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (K + 1), ∑ n ∈ (Finset.range (K + 1)).erase m,
    ccmActualHeadMatchedQuantileParabolicOrientationLedger (m + 2) (n + 2)

/-- Ordered all-pair squared displacement debt of the finite literal source head. -/
def ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum (K : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (K + 1), ∑ n ∈ (Finset.range (K + 1)).erase m,
    ccmActualHeadMatchedQuantileParabolicDisplacementDebt (m + 2) (n + 2)

theorem ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum_nonneg (K : ℕ) :
    0 ≤ ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum K := by
  unfold ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum
  exact Finset.sum_nonneg fun m _ =>
    Finset.sum_nonneg fun n _ =>
      ccmActualHeadMatchedQuantileParabolicDisplacementDebt_nonneg (m + 2) (n + 2)

/-- **All-scale orientation--debt law.**  The complete strict-cross source current has exactly
one signed channel: the all-pair literal displacement-orientation ledger.  Everything else is a
nonnegative quadratic debt. -/
theorem ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_neg_orientationLedger_sub_debt
    (K : ℕ) :
    ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) =
      -ccmActualHeadMatchedQuantileParabolicOrientationLedgerSum K -
        ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum K := by
  rw [ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_strictCross]
  unfold ccmActualHeadMatchedQuantileParabolicOrientationLedgerSum
    ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_orientation_sub_debt
    (m + 2) (n + 2)

/-- Once the literal all-scale orientation ledger is retained, the complete strict-cross source
current is unconditionally nonpositive. -/
theorem ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_add_orientationLedger_nonpos
    (K : ℕ) :
    ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) +
      ccmActualHeadMatchedQuantileParabolicOrientationLedgerSum K ≤ 0 := by
  rw [ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_neg_orientationLedger_sub_debt]
  linarith [ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum_nonneg K]

end RHTower
