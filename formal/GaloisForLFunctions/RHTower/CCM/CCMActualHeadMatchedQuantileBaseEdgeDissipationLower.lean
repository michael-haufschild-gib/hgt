import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePrimeGapDefectStability
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantileLorentzGraphWall

/-!
# Literal base-prime graph dissipation lower bound

For each sufficiently late actual cell, the edge from the base prime `2`
charges at least its physical prime-pair mass times cell index and squared
matched-quantile displacement. This retains the actual von Mangoldt weights
and the singular graph metric; it does not claim a cofinal bound or RH.
-/

namespace RHTower

private theorem ccmBaseEdge_centroidGap_ge_sqrt {k : ℕ} (hk : 9 ≤ k) :
    Real.sqrt (k : ℝ) ≤
      ccmActualHeadMatchedPolarCentroid k - ccmActualHeadMatchedPolarCentroid 2 := by
  have hkpos : 0 < k := by omega
  have hsq := ccmActualHeadMatchedPolarCentroid_sq k hkpos
  have hcpos := ccmActualHeadMatchedPolarCentroid_pos k
  have hsqrt : (Real.sqrt (k : ℝ)) ^ (2 : ℕ) = k :=
    Real.sq_sqrt (by positivity)
  have hsqrt0 := Real.sqrt_nonneg (k : ℝ)
  have hcent : 2 * Real.sqrt (k : ℝ) ≤
      ccmActualHeadMatchedPolarCentroid k := by
    nlinarith only [hsq, hcpos, hsqrt, hsqrt0,
      sq_nonneg (criticalMellinAtomWeight k)]
  have htwoSq := ccmActualHeadMatchedPolarCentroid_sq 2 (by omega)
  have htwoPos := ccmActualHeadMatchedPolarCentroid_pos 2
  have hw2 : criticalMellinAtomWeight 2 ≤ 2 :=
    criticalMellinAtomWeight_le_two_of_pos (by omega)
  have hw20 : 0 ≤ criticalMellinAtomWeight 2 :=
    criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _
  have htwo : ccmActualHeadMatchedPolarCentroid 2 ≤ 3 := by
    nlinarith only [htwoSq, htwoPos, hw2, hw20]
  have hsqrt3 : (3 : ℝ) ≤ Real.sqrt (k : ℝ) := by
    have h := Real.sqrt_le_sqrt (show (9 : ℝ) ≤ k by exact_mod_cast hk)
    norm_num at h ⊢
    exact h
  linarith only [hcent, htwo, hsqrt3]

/-- Literal base-prime edge dissipation pays the squared matched-quantile
displacement with an arithmetic lever at least the target cell index. -/
theorem ccmActualHeadMatchedQuantile_baseEdgeDissipation_ge_weightedDisplacement
    {n : ℕ} (hn : 7 ≤ n) :
    (criticalMellinAtomWeight 2 * criticalMellinAtomWeight (n + 2)) / 2 *
        ((n + 2 : ℕ) : ℝ) *
        (ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
          ccmActualHeadMatchedQuantilePolarDisplacement 2) ^ (2 : ℕ) ≤
      ccmActualHeadMatchedQuantileLorentzEdgeDissipation 0 n := by
  let k : ℕ := n + 2
  let c := ccmActualHeadMatchedPolarCentroid k -
    ccmActualHeadMatchedPolarCentroid 2
  let q := ccmActualHeadQuantilePolarCentroid k -
    ccmActualHeadQuantilePolarCentroid 2
  let d := ccmActualHeadMatchedQuantilePolarDisplacement k -
    ccmActualHeadMatchedQuantilePolarDisplacement 2
  let w := criticalMellinAtomWeight 2 * criticalMellinAtomWeight k
  have hk9 : 9 ≤ k := by dsimp [k]; omega
  have hk2 : 2 ≤ k := by omega
  have hc : Real.sqrt (k : ℝ) ≤ c := ccmBaseEdge_centroidGap_ge_sqrt hk9
  have hc0 : 0 ≤ c := (Real.sqrt_nonneg _).trans hc
  have hq0 : 0 ≤ q := sub_nonneg.mpr
    (ccmActualHeadQuantilePolarCentroid_le_of_le hk2)
  have hw0 : 0 ≤ w := mul_nonneg
    (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer 2)
    (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer k)
  have hqeq : q = c + d := by
    dsimp only [q, c, d]
    rw [ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement 2,
      ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement k]
    ring
  have hD : ccmActualHeadMatchedQuantileLorentzEdgeDissipation 0 n =
      w / 2 * d ^ (2 : ℕ) * c * (c + q) := by
    unfold ccmActualHeadMatchedQuantileLorentzEdgeDissipation
      ccmActualHeadMatchedQuantileLorentzEdgeCurrent
    rw [ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_lorentzEdge]
    unfold ccmActualHeadMatchedQuantileLorentzSquare
      ccmActualHeadMatchedQuantileLorentzEdge
    simp
    dsimp only [c, q, d, w, k]
    rw [ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement 2,
      ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement (n + 2)]
    ring
  have hsq : (k : ℝ) ≤ c ^ (2 : ℕ) := by
    have hroot : (Real.sqrt (k : ℝ)) ^ (2 : ℕ) = k :=
      Real.sq_sqrt (by positivity)
    nlinarith only [hc, hc0, Real.sqrt_nonneg (k : ℝ), hroot]
  have hgeom : (k : ℝ) ≤ c * (c + q) := by
    nlinarith only [hsq, hc0, hq0, mul_nonneg hc0 hq0]
  change w / 2 * (k : ℝ) * d ^ (2 : ℕ) ≤
    ccmActualHeadMatchedQuantileLorentzEdgeDissipation 0 n
  rw [hD]
  have hcoeff : 0 ≤ w / 2 * d ^ (2 : ℕ) := by positivity
  nlinarith only [mul_le_mul_of_nonneg_left hgeom hcoeff]

end RHTower
