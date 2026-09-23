import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantileLorentzEdgeProducer

/-!
# Exact singular graph wall for the literal matched--quantile source

The finite strict-cross source admits an exact edgewise current--dissipation--resistance
factorization.  Finite Cauchy therefore gives a source-faithful global wall in the coupled
matched/quantile coordinates.  The resistance is deliberately retained as an explicit term:
this module proves neither its cofinal control nor a sign for the completed arithmetic source.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Literal ordered off-diagonal strict-cross current, indexed at zero for a finite head. -/
def ccmActualHeadMatchedQuantileLorentzEdgeCurrent (m n : ℕ) : ℝ :=
  ccmActualHeadMatchedQuantileParabolicCrossKernelValue (m + 2) (n + 2)

/-- Singular coupled-coordinate dissipation of one literal ordered edge. -/
def ccmActualHeadMatchedQuantileLorentzEdgeDissipation (m n : ℕ) : ℝ :=
  -(ccmActualHeadMatchedQuantileLorentzEdgeCurrent m n *
    (ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
      ccmActualHeadMatchedQuantilePolarDisplacement (m + 2)) *
    (ccmActualHeadMatchedPolarCentroid (n + 2) -
      ccmActualHeadMatchedPolarCentroid (m + 2)))

/-- Exact resistance complementary to the singular coupled-coordinate dissipation.  It uses
only the two literal centroid gaps and the positive physical pair mass. -/
def ccmActualHeadMatchedQuantileLorentzEdgeResistance (m n : ℕ) : ℝ :=
  let c := ccmActualHeadMatchedPolarCentroid (n + 2) -
    ccmActualHeadMatchedPolarCentroid (m + 2)
  let q := ccmActualHeadQuantilePolarCentroid (n + 2) -
    ccmActualHeadQuantilePolarCentroid (m + 2)
  let w := criticalMellinAtomWeight (m + 2) * criticalMellinAtomWeight (n + 2)
  w / 2 * ((c + q) / c)

lemma ccmActualHeadMatchedPolarCentroid_shift_two_gap_ne_zero {m n : ℕ} (hmn : m ≠ n) :
    ccmActualHeadMatchedPolarCentroid (n + 2) -
      ccmActualHeadMatchedPolarCentroid (m + 2) ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have hinj := (strictMono_ccmActualHeadMatchedPolarCentroid_shift_two).injective h
  omega

/-- Edge resistance is nonnegative for every literal off-diagonal pair. -/
lemma ccmActualHeadMatchedQuantileLorentzEdgeResistance_nonneg {m n : ℕ} (hmn : m ≠ n) :
    0 ≤ ccmActualHeadMatchedQuantileLorentzEdgeResistance m n := by
  let c := ccmActualHeadMatchedPolarCentroid (n + 2) -
    ccmActualHeadMatchedPolarCentroid (m + 2)
  let q := ccmActualHeadQuantilePolarCentroid (n + 2) -
    ccmActualHeadQuantilePolarCentroid (m + 2)
  let w := criticalMellinAtomWeight (m + 2) * criticalMellinAtomWeight (n + 2)
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact ccmActualHeadMatchedPolarCentroid_shift_two_gap_ne_zero hmn
  have hcomono : 0 ≤ c * q := by
    dsimp only [c, q]
    exact ccmActualHeadMatchedQuantileCentroidPair_comonotone m n
  have hw : 0 ≤ w := by
    dsimp only [w]
    exact mul_nonneg (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _) (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _)
  have hratio : 0 ≤ (c + q) / c := by
    rw [show (c + q) / c = (c * c + c * q) / (c * c) by field_simp [hc]]
    exact div_nonneg (add_nonneg (mul_self_nonneg c) hcomono) (mul_self_nonneg c)
  exact mul_nonneg (div_nonneg hw (by norm_num)) hratio

/-- **Exact edge factorization.**  The square of each literal strict-cross current equals the
product of its original singular graph dissipation and explicit resistance. -/
lemma ccmActualHeadMatchedQuantileLorentzEdgeCurrent_sq_eq_dissipation_mul_resistance
    {m n : ℕ} (hmn : m ≠ n) :
    ccmActualHeadMatchedQuantileLorentzEdgeCurrent m n ^ (2 : ℕ) =
      ccmActualHeadMatchedQuantileLorentzEdgeDissipation m n *
        ccmActualHeadMatchedQuantileLorentzEdgeResistance m n := by
  let c := ccmActualHeadMatchedPolarCentroid (n + 2) -
    ccmActualHeadMatchedPolarCentroid (m + 2)
  let d := ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
    ccmActualHeadMatchedQuantilePolarDisplacement (m + 2)
  let w := criticalMellinAtomWeight (m + 2) * criticalMellinAtomWeight (n + 2)
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact ccmActualHeadMatchedPolarCentroid_shift_two_gap_ne_zero hmn
  have hcurrent : ccmActualHeadMatchedQuantileLorentzEdgeCurrent m n =
      -(w / 2) * d * (2 * c + d) := by
    unfold ccmActualHeadMatchedQuantileLorentzEdgeCurrent
    rw [ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_lorentzEdge]
    unfold ccmActualHeadMatchedQuantileLorentzSquare ccmActualHeadMatchedQuantileLorentzEdge
    simp
    rw [ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement (m + 2),
      ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement (n + 2)]
    dsimp only [c, d, w]
    ring
  have hdiss : ccmActualHeadMatchedQuantileLorentzEdgeDissipation m n =
      -(ccmActualHeadMatchedQuantileLorentzEdgeCurrent m n * d * c) := by
    rfl
  have hresistance : ccmActualHeadMatchedQuantileLorentzEdgeResistance m n =
      w / 2 * ((2 * c + d) / c) := by
    unfold ccmActualHeadMatchedQuantileLorentzEdgeResistance
    rw [ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement (m + 2),
      ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement (n + 2)]
    dsimp only [c, d, w]
    ring
  rw [hdiss, hresistance, hcurrent]
  field_simp [hc]

/-- Ordered literal off-diagonal edges of the finite actual head. -/
def ccmActualHeadMatchedQuantileLorentzEdgeSet (K : ℕ) :=
  (Finset.range (K + 1)).sigma fun m => (Finset.range (K + 1)).erase m

/-- Total explicit resistance of the finite literal strict-cross graph. -/
def ccmActualHeadMatchedQuantileParabolicLorentzGraphResistance (K : ℕ) : ℝ :=
  ∑ e ∈ ccmActualHeadMatchedQuantileLorentzEdgeSet K,
    ccmActualHeadMatchedQuantileLorentzEdgeResistance e.1 e.2

lemma ccmActualHeadMatchedQuantileLorentzEdgeCurrent_sum_eq_parabolic_pairing (K : ℕ) :
    (∑ e ∈ ccmActualHeadMatchedQuantileLorentzEdgeSet K,
      ccmActualHeadMatchedQuantileLorentzEdgeCurrent e.1 e.2) =
      ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) := by
  rw [ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_lorentzEdgeSum]
  unfold ccmActualHeadMatchedQuantileLorentzEdgeSet
    ccmActualHeadMatchedQuantileLorentzEdgeCurrent
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  exact ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_lorentzEdge _ _

lemma ccmActualHeadMatchedQuantileLorentzEdgeDissipation_sum_eq_graphDissipation (K : ℕ) :
    (∑ e ∈ ccmActualHeadMatchedQuantileLorentzEdgeSet K,
      ccmActualHeadMatchedQuantileLorentzEdgeDissipation e.1 e.2) =
      ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K := by
  unfold ccmActualHeadMatchedQuantileLorentzEdgeSet
    ccmActualHeadMatchedQuantileLorentzEdgeDissipation
    ccmActualHeadMatchedQuantileLorentzEdgeCurrent
    ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation
  exact Finset.sum_sigma (Finset.range (K + 1))
    (fun m => (Finset.range (K + 1)).erase m)
    (fun e =>
      -(ccmActualHeadMatchedQuantileParabolicCrossKernelValue (e.1 + 2) (e.2 + 2) *
        (ccmActualHeadMatchedQuantilePolarDisplacement (e.2 + 2) -
          ccmActualHeadMatchedQuantilePolarDisplacement (e.1 + 2)) *
        (ccmActualHeadMatchedPolarCentroid (e.2 + 2) -
          ccmActualHeadMatchedPolarCentroid (e.1 + 2))))

lemma ccmActualHeadMatchedQuantileLorentzEdgeDissipation_nonneg (m n : ℕ) :
    0 ≤ ccmActualHeadMatchedQuantileLorentzEdgeDissipation m n := by
  unfold ccmActualHeadMatchedQuantileLorentzEdgeDissipation
    ccmActualHeadMatchedQuantileLorentzEdgeCurrent
  exact neg_nonneg.mpr
    (ccmActualHeadMatchedQuantileParabolicCrossKernelValue_mul_displacement_mul_centroid_nonpos m n)

lemma ccmActualHeadMatchedQuantileParabolicLorentzGraphResistance_nonneg (K : ℕ) :
    0 ≤ ccmActualHeadMatchedQuantileParabolicLorentzGraphResistance K := by
  unfold ccmActualHeadMatchedQuantileParabolicLorentzGraphResistance
  apply Finset.sum_nonneg
  rintro ⟨m, n⟩ hmem
  change 0 ≤ ccmActualHeadMatchedQuantileLorentzEdgeResistance m n
  simp only [ccmActualHeadMatchedQuantileLorentzEdgeSet, Finset.mem_sigma] at hmem
  exact ccmActualHeadMatchedQuantileLorentzEdgeResistance_nonneg
    (Ne.symm (Finset.mem_erase.mp hmem.2).1)

/-- **Literal coupled-error singular graph wall.**  This is finite Cauchy applied to the exact
edge factorization.  It preserves the signed completed strict-cross source on the left and
exposes, rather than estimates away, the resistance whose cofinal arithmetic control remains
the open issue. -/
theorem ccmActualHeadMatchedQuantileParabolicLorentzGraphWall (K : ℕ) :
    (ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
      (ccmActualHeadMatchedQuantileParabolicSourceBoundary K)) ^ (2 : ℕ) ≤
      ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K *
        ccmActualHeadMatchedQuantileParabolicLorentzGraphResistance K := by
  have hCauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (ccmActualHeadMatchedQuantileLorentzEdgeSet K)
    (r := fun e => ccmActualHeadMatchedQuantileLorentzEdgeCurrent e.1 e.2)
    (f := fun e => ccmActualHeadMatchedQuantileLorentzEdgeDissipation e.1 e.2)
    (g := fun e => ccmActualHeadMatchedQuantileLorentzEdgeResistance e.1 e.2)
    (by
      intro e he
      exact ccmActualHeadMatchedQuantileLorentzEdgeDissipation_nonneg e.1 e.2)
    (by
      rintro ⟨m, n⟩ hmem
      change 0 ≤ ccmActualHeadMatchedQuantileLorentzEdgeResistance m n
      simp only [ccmActualHeadMatchedQuantileLorentzEdgeSet, Finset.mem_sigma] at hmem
      exact ccmActualHeadMatchedQuantileLorentzEdgeResistance_nonneg
        (Ne.symm (Finset.mem_erase.mp hmem.2).1))
    (by
      rintro ⟨m, n⟩ hmem
      change ccmActualHeadMatchedQuantileLorentzEdgeCurrent m n ^ (2 : ℕ) ≤
        ccmActualHeadMatchedQuantileLorentzEdgeDissipation m n *
          ccmActualHeadMatchedQuantileLorentzEdgeResistance m n
      simp only [ccmActualHeadMatchedQuantileLorentzEdgeSet, Finset.mem_sigma] at hmem
      rw [ccmActualHeadMatchedQuantileLorentzEdgeCurrent_sq_eq_dissipation_mul_resistance
        (Ne.symm (Finset.mem_erase.mp hmem.2).1)])
  rw [ccmActualHeadMatchedQuantileLorentzEdgeCurrent_sum_eq_parabolic_pairing,
    ccmActualHeadMatchedQuantileLorentzEdgeDissipation_sum_eq_graphDissipation] at hCauchy
  exact hCauchy

end RHTower
