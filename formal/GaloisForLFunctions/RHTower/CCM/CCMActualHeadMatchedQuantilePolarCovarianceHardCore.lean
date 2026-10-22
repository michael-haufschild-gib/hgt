import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarParabolicOrientationLedger

/-!
# Covariance hard core of matched--quantile transport

The literal SP-E/CCM strict-cross source is neither a sum of local gaps nor an unsigned
transport cost.  This module closes the remaining finite algebraic reduction: the entire
orientation ledger is one weighted covariance between the literal matched-to-quantile
displacement and the strictly ordered matched-cell centroid.  The full current is that signed
covariance, with its irreducible nonnegative squared-displacement debt retained.

Thus the cofinal analytic task has one precise form: establish a source-faithful covariance--debt
cancellation for the actual prime--polar displacement.  No positivity, asymptotic premise, RH
premise, or replacement source is introduced here.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

private theorem sum_sum_mul_separate
    (s : Finset ℕ) (f g : ℕ → ℝ) :
    (∑ m ∈ s, ∑ n ∈ s, f m * g n) =
      (∑ m ∈ s, f m) * ∑ n ∈ s, g n := by
  symm
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]

private theorem sum_erase_displacement_orientation_covariance
    (s : Finset ℕ) (w d c : ℕ → ℝ) :
    (∑ m ∈ s, ∑ n ∈ s.erase m,
      (d n - d m) * (w m * w n * (c n - c m))) =
      2 * ((∑ n ∈ s, w n) * (∑ n ∈ s, w n * d n * c n) -
        (∑ n ∈ s, w n * d n) * (∑ n ∈ s, w n * c n)) := by
  have hdiag (m : ℕ) :
      (d m - d m) * (w m * w m * (c m - c m)) = 0 := by ring
  have hinner (m : ℕ) :
      (∑ n ∈ s, (d n - d m) * (w m * w n * (c n - c m))) =
        (∑ n ∈ s, w m * (w n * d n * c n)) -
          (∑ n ∈ s, (w m * c m) * (w n * d n)) -
          (∑ n ∈ s, (w m * d m) * (w n * c n)) +
          ∑ n ∈ s, (w m * d m * c m) * w n := by
    calc
      (∑ n ∈ s, (d n - d m) * (w m * w n * (c n - c m))) =
          ∑ n ∈ s, (w m * (w n * d n * c n) -
            (w m * c m) * (w n * d n) -
            (w m * d m) * (w n * c n) +
            (w m * d m * c m) * w n) := by
              apply Finset.sum_congr rfl
              intro n hn
              ring
      _ = ∑ n ∈ s,
          ((w m * (w n * d n * c n) - (w m * c m) * (w n * d n)) +
            ((w m * d m * c m) * w n - (w m * d m) * (w n * c n))) := by
              apply Finset.sum_congr rfl
              intro n hn
              ring
      _ = (∑ n ∈ s, (w m * (w n * d n * c n) -
            (w m * c m) * (w n * d n))) +
          ∑ n ∈ s, ((w m * d m * c m) * w n -
            (w m * d m) * (w n * c n)) := by
              rw [Finset.sum_add_distrib]
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
        ring
  calc
    (∑ m ∈ s, ∑ n ∈ s.erase m,
        (d n - d m) * (w m * w n * (c n - c m))) =
        ∑ m ∈ s, ∑ n ∈ s,
          (d n - d m) * (w m * w n * (c n - c m)) := by
            apply Finset.sum_congr rfl
            intro m hm
            exact Finset.sum_erase (s := s) (f := fun n =>
              (d n - d m) * (w m * w n * (c n - c m))) (hdiag m)
    _ = ∑ m ∈ s,
          ((∑ n ∈ s, w m * (w n * d n * c n)) -
            (∑ n ∈ s, (w m * c m) * (w n * d n)) -
            (∑ n ∈ s, (w m * d m) * (w n * c n)) +
            ∑ n ∈ s, (w m * d m * c m) * w n) := by
              apply Finset.sum_congr rfl
              intro m hm
              exact hinner m
    _ = (∑ m ∈ s, ∑ n ∈ s, w m * (w n * d n * c n)) -
          (∑ m ∈ s, ∑ n ∈ s, (w m * c m) * (w n * d n)) -
          (∑ m ∈ s, ∑ n ∈ s, (w m * d m) * (w n * c n)) +
          ∑ m ∈ s, ∑ n ∈ s, (w m * d m * c m) * w n := by
            calc
              _ = ∑ m ∈ s,
                  ((∑ n ∈ s, w m * (w n * d n * c n) -
                    ∑ n ∈ s, (w m * c m) * (w n * d n)) +
                    ((∑ n ∈ s, (w m * d m * c m) * w n) -
                      ∑ n ∈ s, (w m * d m) * (w n * c n))) := by
                        apply Finset.sum_congr rfl
                        intro m hm
                        ring
              _ = _ := by
                rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                  Finset.sum_sub_distrib]
                ring
    _ = 2 * ((∑ n ∈ s, w n) * (∑ n ∈ s, w n * d n * c n) -
        (∑ n ∈ s, w n * d n) * (∑ n ∈ s, w n * c n)) := by
      rw [sum_sum_mul_separate s (fun n => w n) (fun n => w n * d n * c n),
        sum_sum_mul_separate s (fun n => w n * c n) (fun n => w n * d n),
        sum_sum_mul_separate s (fun n => w n * d n) (fun n => w n * c n),
        sum_sum_mul_separate s (fun n => w n * d n * c n) (fun n => w n)]
      ring

/-- The unique signed source coordinate of the finite literal head: weighted covariance of
matched-to-quantile displacement against the ordered matched-cell centroid. -/
def ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance (K : ℕ) : ℝ :=
  ccmActualHeadParabolicMass K *
      (∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) *
          ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) *
            ccmActualHeadMatchedPolarCentroid (n + 2)) -
    (∑ n ∈ Finset.range (K + 1),
      criticalMellinAtomWeight (n + 2) *
        ccmActualHeadMatchedQuantilePolarDisplacement (n + 2)) *
      (∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) *
          ccmActualHeadMatchedPolarCentroid (n + 2))

/-- **All-pair covariance law.** The entire literal orientation ledger is exactly twice the
weighted displacement--centroid covariance. Thus there is no independent all-scale orientation
mechanism beyond this one signed covariance. -/
theorem ccmActualHeadMatchedQuantileParabolicOrientationLedgerSum_eq_two_mul_covariance
    (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicOrientationLedgerSum K =
      2 * ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance K := by
  unfold ccmActualHeadMatchedQuantileParabolicOrientationLedgerSum
    ccmActualHeadMatchedQuantileParabolicOrientationLedger
    ccmActualHeadMatchedQuantileParabolicOrientationCoefficient
    ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance
    ccmActualHeadParabolicMass
  exact sum_erase_displacement_orientation_covariance
    (Finset.range (K + 1))
    (fun n => criticalMellinAtomWeight (n + 2))
    (fun n => ccmActualHeadMatchedQuantilePolarDisplacement (n + 2))
    (fun n => ccmActualHeadMatchedPolarCentroid (n + 2))

/-- **Covariance--debt hard-core law.** The complete strict-cross source current is negative
twice the literal signed covariance, minus its full nonnegative squared-displacement debt. Any
proof of a cofinal bound must control this exact cancellation; diagonal energies and local gap
estimates cannot replace it. -/
theorem ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_neg_two_mul_covariance_sub_debt
    (K : ℕ) :
    ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) =
      -2 * ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance K -
        ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum K := by
  rw [ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_neg_orientationLedger_sub_debt,
    ccmActualHeadMatchedQuantileParabolicOrientationLedgerSum_eq_two_mul_covariance]
  ring

private theorem weighted_covariance_eq_adjacent_abel
    (K : ℕ) (w d c : ℕ → ℝ) :
    let W := ∑ i ∈ Finset.range (K + 1), w i
    let C := ∑ i ∈ Finset.range (K + 1), w i * c i
    W * (∑ i ∈ Finset.range (K + 1), w i * d i * c i) -
        (∑ i ∈ Finset.range (K + 1), w i * d i) * C =
      ∑ r ∈ Finset.range K, (d (r + 1) - d r) *
        (C * (∑ i ∈ Finset.range (r + 1), w i) -
          W * (∑ i ∈ Finset.range (r + 1), w i * c i)) := by
  dsimp only
  let W := ∑ i ∈ Finset.range (K + 1), w i
  let C := ∑ i ∈ Finset.range (K + 1), w i * c i
  let h : ℕ → ℝ := fun i => w i * (W * c i - C)
  have hsum : (∑ i ∈ Finset.range (K + 1), h i) = 0 := by
    calc
      (∑ i ∈ Finset.range (K + 1), h i) =
          ∑ i ∈ Finset.range (K + 1),
            (W * (w i * c i) - C * w i) := by
              apply Finset.sum_congr rfl
              intro i hi
              dsimp only [h]
              ring
      _ = W * C - C * W := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 0 := by ring
  have hprefix (r : ℕ) :
      (∑ i ∈ Finset.range (r + 1), h i) =
        W * (∑ i ∈ Finset.range (r + 1), w i * c i) -
          C * (∑ i ∈ Finset.range (r + 1), w i) := by
    calc
      (∑ i ∈ Finset.range (r + 1), h i) =
          ∑ i ∈ Finset.range (r + 1),
            (W * (w i * c i) - C * w i) := by
              apply Finset.sum_congr rfl
              intro i hi
              dsimp only [h]
              ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hcov :
      W * (∑ i ∈ Finset.range (K + 1), w i * d i * c i) -
          (∑ i ∈ Finset.range (K + 1), w i * d i) * C =
        ∑ i ∈ Finset.range (K + 1), d i * h i := by
    symm
    calc
      (∑ i ∈ Finset.range (K + 1), d i * h i) =
          ∑ i ∈ Finset.range (K + 1),
            (W * (w i * d i * c i) - (w i * d i) * C) := by
              apply Finset.sum_congr rfl
              intro i hi
              dsimp only [h]
              ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have hparts := Finset.sum_range_by_parts d h (K + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at hparts
  rw [hsum] at hparts
  calc
    W * (∑ i ∈ Finset.range (K + 1), w i * d i * c i) -
        (∑ i ∈ Finset.range (K + 1), w i * d i) * C =
        ∑ i ∈ Finset.range (K + 1), d i * h i := hcov
    _ = -(∑ r ∈ Finset.range K,
        (d (r + 1) - d r) * (∑ i ∈ Finset.range (r + 1), h i)) := by
          linarith
    _ = ∑ r ∈ Finset.range K, (d (r + 1) - d r) *
        (C * (∑ i ∈ Finset.range (r + 1), w i) -
          W * (∑ i ∈ Finset.range (r + 1), w i * c i)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro r hr
            rw [hprefix]
            ring

/-- Cutoff-dependent global coefficient of the adjacent-gap Abel representation. It retains the
full head mass and centroid distribution, so it is not a local gap weight. -/
def ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel (K r : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (K + 1),
      criticalMellinAtomWeight (i + 2) * ccmActualHeadMatchedPolarCentroid (i + 2)) *
      (∑ i ∈ Finset.range (r + 1), criticalMellinAtomWeight (i + 2)) -
    ccmActualHeadParabolicMass K *
      (∑ i ∈ Finset.range (r + 1),
        criticalMellinAtomWeight (i + 2) * ccmActualHeadMatchedPolarCentroid (i + 2))

/-- **Global adjacent-gap Abel law.** The sole signed covariance can be read from adjacent
matched-cell gaps only after weighting each gap by the literal, cutoff-dependent global kernel.
This is an exact nonlocal inverse, not a local-energy reduction. -/
theorem ccmActualHeadMatchedQuantileParabolicCovariance_eq_adjacentGapKernel
    (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance K =
      ∑ r ∈ Finset.range K,
        (ccmActualHeadMatchedQuantilePolarDisplacement (r + 3) -
          ccmActualHeadMatchedQuantilePolarDisplacement (r + 2)) *
          ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K r := by
  unfold ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance
    ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel
    ccmActualHeadParabolicMass
  exact weighted_covariance_eq_adjacent_abel K
    (fun i => criticalMellinAtomWeight (i + 2))
    (fun i => ccmActualHeadMatchedQuantilePolarDisplacement (i + 2))
    (fun i => ccmActualHeadMatchedPolarCentroid (i + 2))

/-- The Abel representation retains the literal oriented adjacent matched-cell overlap/gap at
every index; its nonlocality lies only in the exact global coefficient. -/
theorem ccmActualHeadMatchedQuantileParabolicCovariance_eq_adjacentMatchedGapKernel
    (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance K =
      ∑ r ∈ Finset.range K,
        (ccmActualHeadMatchedPolarUpperCoordinate (r + 2) -
          ccmActualHeadMatchedPolarLowerCoordinate (r + 3)) *
          ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K r := by
  rw [ccmActualHeadMatchedQuantileParabolicCovariance_eq_adjacentGapKernel]
  apply Finset.sum_congr rfl
  intro r hr
  rw [ccmActualHeadMatchedQuantilePolarDisplacement_succ_sub_eq_adjacentGap (r + 2)]

/-- **Cutoff-covariant kernel update.** Enlarging the literal head by the new atom `K + 3`
updates every retained adjacent-gap coefficient by that atom times its matched-centroid excess
over the corresponding prefix. Thus the nonlocal inverse has a source-determined history law;
it is not a fixed adjacent coefficient system. -/
theorem ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_succ_sub
    (K r : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel (K + 1) r -
      ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K r =
      criticalMellinAtomWeight (K + 3) *
        (ccmActualHeadMatchedPolarCentroid (K + 3) *
          (∑ i ∈ Finset.range (r + 1), criticalMellinAtomWeight (i + 2)) -
          ∑ i ∈ Finset.range (r + 1),
            criticalMellinAtomWeight (i + 2) *
              ccmActualHeadMatchedPolarCentroid (i + 2)) := by
  unfold ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel
    ccmActualHeadParabolicMass
  simp only [Finset.sum_range_succ]
  ring

/-- Every newly appended source index can only increase coefficients already visible to the
literal adjacent-gap current. A non-prime-power append leaves them unchanged; a prime-power
append is strictly propagating by the theorem below. -/
theorem ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_succ_sub_nonneg
    (K r : ℕ) (hr : r ≤ K) :
    0 ≤ ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel (K + 1) r -
      ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K r := by
  rw [ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_succ_sub]
  apply mul_nonneg (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _)
  have hrewrite :
      ccmActualHeadMatchedPolarCentroid (K + 3) *
          (∑ i ∈ Finset.range (r + 1), criticalMellinAtomWeight (i + 2)) -
          ∑ i ∈ Finset.range (r + 1),
            criticalMellinAtomWeight (i + 2) *
              ccmActualHeadMatchedPolarCentroid (i + 2) =
        ∑ i ∈ Finset.range (r + 1),
          criticalMellinAtomWeight (i + 2) *
            (ccmActualHeadMatchedPolarCentroid (K + 3) -
              ccmActualHeadMatchedPolarCentroid (i + 2)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hrewrite]
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _)
  apply sub_nonneg.mpr
  have hi_lt : i < K + 1 := by
    have hir : i < r + 1 := Finset.mem_range.mp hi
    omega
  simpa [Nat.add_assoc, Nat.add_comm] using
    (strictMono_ccmActualHeadMatchedPolarCentroid_shift_two hi_lt).le

/-- **Positive Abel cone.** Every coefficient of an adjacent gap that is actually present in a
finite SP-E head is nonnegative. Thus, after the exact Abel reduction, all remaining sign
freedom lies in the literal oriented gap data. -/
theorem ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_nonneg
    (K r : ℕ) (hr : r ≤ K) :
    0 ≤ ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K r := by
  refine Nat.le_induction ?_ ?_ K hr
  · unfold ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel
      ccmActualHeadParabolicMass
    ring_nf
    exact le_rfl
  · intro k hrk ih
    linarith [ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_succ_sub_nonneg k r hrk]

/-- **Prime-power history propagation.** Whenever the newly appended literal index is a prime
power, it increases strictly every coefficient already visible to the finite SP-E adjacent-gap
current. The proof uses only positive prime mass and strict matched-centroid order. -/
theorem ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_lt_succ_of_isPrimePow
    (K r : ℕ) (hr : r ≤ K) (hnew : IsPrimePow (K + 3)) :
    ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K r <
      ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel (K + 1) r := by
  rw [← sub_pos,
    ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_succ_sub]
  apply mul_pos (criticalMellinAtomWeight_pos hnew)
  have hrewrite :
      ccmActualHeadMatchedPolarCentroid (K + 3) *
          (∑ i ∈ Finset.range (r + 1), criticalMellinAtomWeight (i + 2)) -
          ∑ i ∈ Finset.range (r + 1),
            criticalMellinAtomWeight (i + 2) *
              ccmActualHeadMatchedPolarCentroid (i + 2) =
        ∑ i ∈ Finset.range (r + 1),
          criticalMellinAtomWeight (i + 2) *
            (ccmActualHeadMatchedPolarCentroid (K + 3) -
              ccmActualHeadMatchedPolarCentroid (i + 2)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hrewrite]
  have hnonneg : ∀ i ∈ Finset.range (r + 1),
      0 ≤ criticalMellinAtomWeight (i + 2) *
        (ccmActualHeadMatchedPolarCentroid (K + 3) -
          ccmActualHeadMatchedPolarCentroid (i + 2)) := by
    intro i hi
    apply mul_nonneg (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _)
    apply sub_nonneg.mpr
    have hi_lt : i < K + 1 := by
      have hir : i < r + 1 := Finset.mem_range.mp hi
      omega
    simpa [Nat.add_assoc, Nat.add_comm] using
      (strictMono_ccmActualHeadMatchedPolarCentroid_shift_two hi_lt).le
  have hmem : 0 ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
  have hterm : 0 < criticalMellinAtomWeight (0 + 2) *
      (ccmActualHeadMatchedPolarCentroid (K + 3) -
        ccmActualHeadMatchedPolarCentroid (0 + 2)) := by
    apply mul_pos
    · norm_num
      exact criticalMellinAtomWeight_pos Nat.prime_two.isPrimePow
    · apply sub_pos.mpr
      simpa [Nat.add_assoc, Nat.add_comm] using
        strictMono_ccmActualHeadMatchedPolarCentroid_shift_two (show 0 < K + 1 by omega)
  exact lt_of_lt_of_le hterm
    (Finset.single_le_sum (s := Finset.range (r + 1))
      (f := fun i => criticalMellinAtomWeight (i + 2) *
        (ccmActualHeadMatchedPolarCentroid (K + 3) -
          ccmActualHeadMatchedPolarCentroid (i + 2))) hnonneg hmem)

/-- **Cutoff-instability witness.** The literal coefficient of the first adjacent gap changes
strictly when the head is enlarged from `2` to `3`; its exact increment is the positive new
prime atom at `5` times the positive separation of the first and new barycentres. -/
theorem ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_two_lt_three :
    ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel 2 0 <
      ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel 3 0 := by
  have hw2 : 0 < criticalMellinAtomWeight 2 :=
    criticalMellinAtomWeight_pos Nat.prime_two.isPrimePow
  have hw5 : 0 < criticalMellinAtomWeight 5 :=
    criticalMellinAtomWeight_pos Nat.prime_five.isPrimePow
  have hc : ccmActualHeadMatchedPolarCentroid 2 <
      ccmActualHeadMatchedPolarCentroid 5 := by
    have h := strictMono_ccmActualHeadMatchedPolarCentroid_shift_two (show 0 < 3 by omega)
    norm_num at h ⊢
    exact h
  have hdelta :
      ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel 3 0 -
        ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel 2 0 =
      criticalMellinAtomWeight 2 * criticalMellinAtomWeight 5 *
        (ccmActualHeadMatchedPolarCentroid 5 -
          ccmActualHeadMatchedPolarCentroid 2) := by
    unfold ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel
      ccmActualHeadParabolicMass
    norm_num [Finset.sum_range_succ]
    ring
  rw [← sub_pos, hdelta]
  exact mul_pos (mul_pos hw2 hw5) (sub_pos.mpr hc)

/-- **Fixed-coefficient no-go.** No cutoff-independent adjacent-gap coefficient can equal the
literal SP-E covariance kernel at every finite head. This excludes a direct coefficient-preserving
identification with a fixed inverse-incidence primitive; it does not exclude a new explicit
source transformation. -/
theorem no_cutoffIndependent_ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel :
    ¬ ∃ κ : ℕ → ℝ, ∀ K r : ℕ,
      ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K r = κ r := by
  rintro ⟨κ, hκ⟩
  have heq :
      ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel 2 0 =
        ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel 3 0 :=
    (hκ 2 0).trans (hκ 3 0).symm
  exact (ne_of_lt ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_two_lt_three) heq

end RHTower
