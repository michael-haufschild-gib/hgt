import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarParabolicVarianceBalance

/-!
# Lorentz-edge producer for the literal matched--quantile source

The actual strict-cross source is not a covariance plus an independent debt.  At every ordered
pair of literal cells it is one weighted Lorentz square: the squared matched-centroid separation
minus the squared equal-mass-quantile separation.  This module keeps the two coordinates coupled
before any scalar energy estimate.  It identifies the exact pairwise cone that a cofinal signed
producer must control, without asserting a sign or a bound.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Matched and quantile centroid separations of one ordered physical-cell pair. -/
def ccmActualHeadMatchedQuantileLorentzEdge (m n : ℕ) : Fin 2 → ℝ :=
  ![ccmActualHeadMatchedPolarCentroid n - ccmActualHeadMatchedPolarCentroid m,
    ccmActualHeadQuantilePolarCentroid n - ccmActualHeadQuantilePolarCentroid m]

/-- The indefinite square on the coupled matched/quantile separation plane. -/
def ccmActualHeadMatchedQuantileLorentzSquare (v : Fin 2 → ℝ) : ℝ :=
  v 0 ^ (2 : ℕ) - v 1 ^ (2 : ℕ)

/-- **Pairwise coupled-source law.** One literal cross-cell source is exactly its positive pair
mass times the Lorentz square of matched versus quantile centroid separation.  Thus the signed
orientation and unavoidable displacement debt are one inseparable edge quantity. -/
theorem ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_lorentzEdge
    (m n : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCrossKernelValue m n =
      (criticalMellinAtomWeight m * criticalMellinAtomWeight n) / 2 *
        ccmActualHeadMatchedQuantileLorentzSquare
          (ccmActualHeadMatchedQuantileLorentzEdge m n) := by
  rw [ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_orientation_sub_debt]
  unfold ccmActualHeadMatchedQuantileParabolicOrientationLedger
    ccmActualHeadMatchedQuantileParabolicOrientationCoefficient
    ccmActualHeadMatchedQuantileParabolicDisplacementDebt
    ccmActualHeadMatchedQuantileLorentzSquare
    ccmActualHeadMatchedQuantileLorentzEdge
  simp
  rw [ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement m,
    ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement n]
  ring

/-- **All-pair Lorentz producer.** The complete literal codiagonal is the ordered actual-head
sum of the coupled Lorentz edge source.  No covariance/debt splitting, absolute value, or local
sign condition occurs in this representation. -/
theorem ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_lorentzEdgeSum
    (K : ℕ) :
    ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) =
      ∑ m ∈ Finset.range (K + 1), ∑ n ∈ (Finset.range (K + 1)).erase m,
        (criticalMellinAtomWeight (m + 2) * criticalMellinAtomWeight (n + 2)) / 2 *
          ccmActualHeadMatchedQuantileLorentzSquare
            (ccmActualHeadMatchedQuantileLorentzEdge (m + 2) (n + 2)) := by
  rw [ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_strictCross]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  change ccmActualHeadMatchedQuantileParabolicCrossKernelValue (m + 2) (n + 2) = _
  exact ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_lorentzEdge _ _

/-- Consecutive equal-mass quantile barycentres are ordered without a prime-gap premise. -/
theorem ccmActualHeadQuantilePolarCentroid_succ_sub_nonneg (n : ℕ) :
    0 ≤ ccmActualHeadQuantilePolarCentroid (n + 1) -
      ccmActualHeadQuantilePolarCentroid n := by
  unfold ccmActualHeadQuantilePolarCentroid
  have h0 := ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight n
  have h1 := ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight (n + 1)
  norm_num [Nat.add_assoc] at h0 h1 ⊢
  nlinarith [criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n,
    criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer (n + 1)]

/-- Equal-mass quantile barycentres are monotone in the physical-cell index. -/
theorem ccmActualHeadQuantilePolarCentroid_le_of_le {m n : ℕ} (hmn : m ≤ n) :
    ccmActualHeadQuantilePolarCentroid m ≤ ccmActualHeadQuantilePolarCentroid n := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      exact ih.trans (sub_nonneg.mp (ccmActualHeadQuantilePolarCentroid_succ_sub_nonneg n))

/-- On every actual-head edge, matched and equal-mass-quantile centroid separations have the
same weak orientation.  This is the order input that keeps the Lorentz edge coupled. -/
theorem ccmActualHeadMatchedQuantileCentroidPair_comonotone (m n : ℕ) :
    0 ≤ (ccmActualHeadMatchedPolarCentroid (n + 2) -
      ccmActualHeadMatchedPolarCentroid (m + 2)) *
      (ccmActualHeadQuantilePolarCentroid (n + 2) -
        ccmActualHeadQuantilePolarCentroid (m + 2)) := by
  rcases le_total m n with hmn | hnm
  · exact mul_nonneg
      (sub_nonneg.mpr (strictMono_ccmActualHeadMatchedPolarCentroid_shift_two.monotone hmn))
      (sub_nonneg.mpr (ccmActualHeadQuantilePolarCentroid_le_of_le
        (Nat.add_le_add_right hmn 2)))
  · exact mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr (strictMono_ccmActualHeadMatchedPolarCentroid_shift_two.monotone hnm))
      (sub_nonpos.mpr (ccmActualHeadQuantilePolarCentroid_le_of_le
        (Nat.add_le_add_right hnm 2)))

/-- **Coupled-error edge dissipation.**  A literal cross current times its literal displacement
increment and its matched-centroid orientation is nonpositive on every actual-head edge.  This
does not sign the current itself: it supplies the singular graph factor retained by a valid
global wall law. -/
theorem ccmActualHeadMatchedQuantileParabolicCrossKernelValue_mul_displacement_mul_centroid_nonpos
    (m n : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCrossKernelValue (m + 2) (n + 2) *
      (ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
        ccmActualHeadMatchedQuantilePolarDisplacement (m + 2)) *
      (ccmActualHeadMatchedPolarCentroid (n + 2) -
        ccmActualHeadMatchedPolarCentroid (m + 2)) ≤ 0 := by
  let c := ccmActualHeadMatchedPolarCentroid (n + 2) -
    ccmActualHeadMatchedPolarCentroid (m + 2)
  let d := ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
    ccmActualHeadMatchedQuantilePolarDisplacement (m + 2)
  let w := criticalMellinAtomWeight (m + 2) * criticalMellinAtomWeight (n + 2)
  have hcomono := ccmActualHeadMatchedQuantileCentroidPair_comonotone m n
  have hcd : 0 ≤ c * (c + d) := by
    calc
      0 ≤ (ccmActualHeadMatchedPolarCentroid (n + 2) -
        ccmActualHeadMatchedPolarCentroid (m + 2)) *
        (ccmActualHeadQuantilePolarCentroid (n + 2) -
          ccmActualHeadQuantilePolarCentroid (m + 2)) := hcomono
      _ = c * (c + d) := by
        dsimp only [c, d]
        rw [ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement (m + 2),
          ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement (n + 2)]
        ring
  have hw : 0 ≤ w := by
    dsimp only [w]
    exact mul_nonneg (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _) (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _)
  have hmetric : 0 ≤ c * (2 * c + d) := by
    calc
      c * (2 * c + d) = c ^ (2 : ℕ) + c * (c + d) := by ring
      _ ≥ 0 := add_nonneg (sq_nonneg c) hcd
  have hfactor : 0 ≤ w / 2 * d ^ (2 : ℕ) :=
    mul_nonneg (div_nonneg hw (by norm_num)) (sq_nonneg d)
  calc
    ccmActualHeadMatchedQuantileParabolicCrossKernelValue (m + 2) (n + 2) *
        (ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
          ccmActualHeadMatchedQuantilePolarDisplacement (m + 2)) *
        (ccmActualHeadMatchedPolarCentroid (n + 2) -
          ccmActualHeadMatchedPolarCentroid (m + 2)) =
        -(w / 2 * d ^ (2 : ℕ) * (c * (2 * c + d))) := by
      rw [ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_lorentzEdge]
      unfold ccmActualHeadMatchedQuantileLorentzSquare ccmActualHeadMatchedQuantileLorentzEdge
      simp
      dsimp only [c, d, w]
      rw [ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement (m + 2),
        ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement (n + 2)]
      ring
    _ ≤ 0 := neg_nonpos.mpr (mul_nonneg hfactor hmetric)

/-- **Literal singular graph dissipation.**  This is the actual strict-cross source paired with
its coupled displacement--orientation coordinate.  It is a seminorm-like quantity: zero edges
remain deliberately unpenalized, so no inverse or artificial coercive shift is introduced. -/
def ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation (K : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (K + 1), ∑ n ∈ (Finset.range (K + 1)).erase m,
    -(ccmActualHeadMatchedQuantileParabolicCrossKernelValue (m + 2) (n + 2) *
      (ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
        ccmActualHeadMatchedQuantilePolarDisplacement (m + 2)) *
      (ccmActualHeadMatchedPolarCentroid (n + 2) -
        ccmActualHeadMatchedPolarCentroid (m + 2)))

/-- The singular graph pairing has an exact nonnegative density in the original physical
coordinates.  In particular, its positivity is not imported from a scalar proxy. -/
theorem ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation_eq_density (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K =
      ∑ m ∈ Finset.range (K + 1), ∑ n ∈ (Finset.range (K + 1)).erase m,
        (criticalMellinAtomWeight (m + 2) * criticalMellinAtomWeight (n + 2)) / 2 *
          (ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
            ccmActualHeadMatchedQuantilePolarDisplacement (m + 2)) ^ (2 : ℕ) *
          (ccmActualHeadMatchedPolarCentroid (n + 2) -
            ccmActualHeadMatchedPolarCentroid (m + 2)) *
          ((ccmActualHeadMatchedPolarCentroid (n + 2) -
              ccmActualHeadMatchedPolarCentroid (m + 2)) +
            (ccmActualHeadQuantilePolarCentroid (n + 2) -
              ccmActualHeadQuantilePolarCentroid (m + 2))) := by
  unfold ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_lorentzEdge]
  unfold ccmActualHeadMatchedQuantileLorentzSquare ccmActualHeadMatchedQuantileLorentzEdge
  simp
  rw [ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement (m + 2),
    ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement (n + 2)]
  ring

/-- The source-faithful singular graph dissipation is nonnegative on every finite actual head. -/
theorem ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation_nonneg (K : ℕ) :
    0 ≤ ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K := by
  unfold ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation
  exact Finset.sum_nonneg fun m hm =>
    Finset.sum_nonneg fun n hn =>
      neg_nonneg.mpr
        (ccmActualHeadMatchedQuantileParabolicCrossKernelValue_mul_displacement_mul_centroid_nonpos m n)

end RHTower
