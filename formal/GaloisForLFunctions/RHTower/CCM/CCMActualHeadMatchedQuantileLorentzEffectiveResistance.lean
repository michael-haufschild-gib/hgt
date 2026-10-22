import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantileLorentzSupport
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePLorentzGraphKernel

/-!
# Effective resistance of literal matched--quantile Lorentz graph

The raw Lorentz resistance remains nonzero on some edges whose singular graph dissipation is
zero. Such edges carry no current, so charging them in Cauchy is an artefact of that particular
certificate, rather than an obstruction of the completed source. This module removes exactly and
only those dissipation-null edges. The factorization and finite graph wall survive unchanged;
the resulting effective resistance is pointwise bounded by raw resistance.

Effective resistance has exactly the same radical as the physical dissipation: a common
displacement on active prime-power vertices. Consequently raw-resistance divergence does not
settle the cofinal graph question. The remaining source-faithful issue is whether this effective,
current-carrying resistance is bounded or can be cancelled by the completed terminal connection.
-/

noncomputable section

namespace RHTower

/-- Cauchy resistance restricted to literal edges carrying nonzero singular dissipation. -/
def ccmActualHeadMatchedQuantileLorentzEffectiveResistance (m n : ℕ) : ℝ :=
  if ccmActualHeadMatchedQuantileLorentzEdgeDissipation m n = 0 then 0
  else ccmActualHeadMatchedQuantileLorentzEdgeResistance m n

lemma ccmActualHeadMatchedQuantileLorentzEffectiveResistance_nonneg
    {m n : ℕ} (hmn : m ≠ n) :
    0 ≤ ccmActualHeadMatchedQuantileLorentzEffectiveResistance m n := by
  unfold ccmActualHeadMatchedQuantileLorentzEffectiveResistance
  split_ifs with h
  · exact le_rfl
  · exact ccmActualHeadMatchedQuantileLorentzEdgeResistance_nonneg hmn

/-- The exact Lorentz factorization remains true after deleting only dissipation-null edges. -/
lemma ccmActualHeadMatchedQuantileLorentzEdgeCurrent_sq_eq_dissipation_mul_effectiveResistance
    {m n : ℕ} (hmn : m ≠ n) :
    ccmActualHeadMatchedQuantileLorentzEdgeCurrent m n ^ (2 : ℕ) =
      ccmActualHeadMatchedQuantileLorentzEdgeDissipation m n *
        ccmActualHeadMatchedQuantileLorentzEffectiveResistance m n := by
  unfold ccmActualHeadMatchedQuantileLorentzEffectiveResistance
  by_cases hzero : ccmActualHeadMatchedQuantileLorentzEdgeDissipation m n = 0
  · rw [if_pos hzero, mul_zero]
    have hfactor :=
      ccmActualHeadMatchedQuantileLorentzEdgeCurrent_sq_eq_dissipation_mul_resistance hmn
    rw [hzero, zero_mul] at hfactor
    exact hfactor
  · rw [if_neg hzero]
    exact ccmActualHeadMatchedQuantileLorentzEdgeCurrent_sq_eq_dissipation_mul_resistance hmn

/-- Effective resistance is never larger than raw Lorentz Cauchy resistance. -/
lemma ccmActualHeadMatchedQuantileLorentzEffectiveResistance_le_raw
    {m n : ℕ} (hmn : m ≠ n) :
    ccmActualHeadMatchedQuantileLorentzEffectiveResistance m n ≤
      ccmActualHeadMatchedQuantileLorentzEdgeResistance m n := by
  unfold ccmActualHeadMatchedQuantileLorentzEffectiveResistance
  split_ifs with hzero
  · exact ccmActualHeadMatchedQuantileLorentzEdgeResistance_nonneg hmn
  · exact le_rfl

/-- Total effective resistance of the finite literal strict-cross graph. -/
def ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance (K : ℕ) : ℝ :=
  ∑ e ∈ ccmActualHeadMatchedQuantileLorentzEdgeSet K,
    ccmActualHeadMatchedQuantileLorentzEffectiveResistance e.1 e.2

lemma ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance_nonneg (K : ℕ) :
    0 ≤ ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance K := by
  unfold ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance
  apply Finset.sum_nonneg
  rintro ⟨m, n⟩ hmem
  simp only [ccmActualHeadMatchedQuantileLorentzEdgeSet, Finset.mem_sigma] at hmem
  exact ccmActualHeadMatchedQuantileLorentzEffectiveResistance_nonneg
    (Ne.symm (Finset.mem_erase.mp hmem.2).1)

/-- Effective graph cost is bounded by raw cost. -/
theorem ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance_le_raw
    (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance K ≤
      ccmActualHeadMatchedQuantileParabolicLorentzGraphResistance K := by
  unfold ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance
    ccmActualHeadMatchedQuantileParabolicLorentzGraphResistance
  apply Finset.sum_le_sum
  rintro ⟨m, n⟩ hmem
  simp only [ccmActualHeadMatchedQuantileLorentzEdgeSet, Finset.mem_sigma] at hmem
  exact ccmActualHeadMatchedQuantileLorentzEffectiveResistance_le_raw
    (Ne.symm (Finset.mem_erase.mp hmem.2).1)

/-- **Effective literal coupled-error graph wall.** Cauchy is applied only after exact deletion
of edges which carry neither current nor dissipation. -/
theorem ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphWall (K : ℕ) :
    (ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
      (ccmActualHeadMatchedQuantileParabolicSourceBoundary K)) ^ (2 : ℕ) ≤
      ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K *
        ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance K := by
  have hCauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (ccmActualHeadMatchedQuantileLorentzEdgeSet K)
    (r := fun e => ccmActualHeadMatchedQuantileLorentzEdgeCurrent e.1 e.2)
    (f := fun e => ccmActualHeadMatchedQuantileLorentzEdgeDissipation e.1 e.2)
    (g := fun e => ccmActualHeadMatchedQuantileLorentzEffectiveResistance e.1 e.2)
    (by
      intro e he
      exact ccmActualHeadMatchedQuantileLorentzEdgeDissipation_nonneg e.1 e.2)
    (by
      rintro ⟨m, n⟩ hmem
      simp only [ccmActualHeadMatchedQuantileLorentzEdgeSet, Finset.mem_sigma] at hmem
      exact ccmActualHeadMatchedQuantileLorentzEffectiveResistance_nonneg
        (Ne.symm (Finset.mem_erase.mp hmem.2).1))
    (by
      rintro ⟨m, n⟩ hmem
      simp only [ccmActualHeadMatchedQuantileLorentzEdgeSet, Finset.mem_sigma] at hmem
      exact le_of_eq
        (ccmActualHeadMatchedQuantileLorentzEdgeCurrent_sq_eq_dissipation_mul_effectiveResistance
          (Ne.symm (Finset.mem_erase.mp hmem.2).1)))
  rw [ccmActualHeadMatchedQuantileLorentzEdgeCurrent_sum_eq_parabolic_pairing,
    ccmActualHeadMatchedQuantileLorentzEdgeDissipation_sum_eq_graphDissipation] at hCauchy
  exact hCauchy

/-- At one genuine off-diagonal edge, effective resistance vanishes exactly when the literal
singular dissipation vanishes. Thus deleting a null edge introduces no new degeneracy. -/
lemma ccmActualHeadMatchedQuantileLorentzEffectiveResistance_eq_zero_iff_dissipation_eq_zero
    {m n : ℕ} (hmn : m ≠ n) :
    ccmActualHeadMatchedQuantileLorentzEffectiveResistance m n = 0 ↔
      ccmActualHeadMatchedQuantileLorentzEdgeDissipation m n = 0 := by
  constructor
  · intro heff
    by_contra hdiss
    have hraw_ne : ccmActualHeadMatchedQuantileLorentzEdgeResistance m n ≠ 0 := by
      intro hraw
      have hfactor :=
        ccmActualHeadMatchedQuantileLorentzEdgeCurrent_sq_eq_dissipation_mul_resistance hmn
      rw [hraw, mul_zero] at hfactor
      have hcurrent : ccmActualHeadMatchedQuantileLorentzEdgeCurrent m n = 0 :=
        sq_eq_zero_iff.mp hfactor
      apply hdiss
      unfold ccmActualHeadMatchedQuantileLorentzEdgeDissipation
      rw [hcurrent]
      ring
    have hraw_pos : 0 < ccmActualHeadMatchedQuantileLorentzEdgeResistance m n :=
      lt_of_le_of_ne (ccmActualHeadMatchedQuantileLorentzEdgeResistance_nonneg hmn)
        (Ne.symm hraw_ne)
    unfold ccmActualHeadMatchedQuantileLorentzEffectiveResistance at heff
    rw [if_neg hdiss] at heff
    exact hraw_pos.ne' heff
  · intro hdiss
    simp [ccmActualHeadMatchedQuantileLorentzEffectiveResistance, hdiss]

/-- **Exact effective radical law.** The sharper Cauchy cost vanishes precisely when the
literal singular graph dissipation vanishes. It therefore removes raw null cost without
weakening coercivity on the physical quotient. -/
theorem ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance_eq_zero_iff_graphDissipation_eq_zero
    (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance K = 0 ↔
      ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K = 0 := by
  constructor
  · intro heff
    have houter : ∀ m ∈ Finset.range (K + 1),
        ∑ n ∈ (Finset.range (K + 1)).erase m,
          ccmActualHeadMatchedQuantileLorentzEffectiveResistance m n = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg (fun m hm =>
        Finset.sum_nonneg fun n hn =>
          ccmActualHeadMatchedQuantileLorentzEffectiveResistance_nonneg
            (Ne.symm (Finset.mem_erase.mp hn).1))).mp
      simpa [ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance,
        ccmActualHeadMatchedQuantileLorentzEdgeSet, Finset.sum_sigma] using heff
    unfold ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation
    apply Finset.sum_eq_zero
    intro m hm
    have hinner : ∀ n ∈ (Finset.range (K + 1)).erase m,
        ccmActualHeadMatchedQuantileLorentzEffectiveResistance m n = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun n hn =>
        ccmActualHeadMatchedQuantileLorentzEffectiveResistance_nonneg
          (Ne.symm (Finset.mem_erase.mp hn).1))).mp (houter m hm)
    apply Finset.sum_eq_zero
    intro n hn
    have he := hinner n hn
    have hd :=
      (ccmActualHeadMatchedQuantileLorentzEffectiveResistance_eq_zero_iff_dissipation_eq_zero
        (Ne.symm (Finset.mem_erase.mp hn).1)).mp he
    exact hd
  · intro hdiss
    have houter : ∀ m ∈ Finset.range (K + 1),
        ∑ n ∈ (Finset.range (K + 1)).erase m,
          -(ccmActualHeadMatchedQuantileParabolicCrossKernelValue (m + 2) (n + 2) *
            (ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
              ccmActualHeadMatchedQuantilePolarDisplacement (m + 2)) *
            (ccmActualHeadMatchedPolarCentroid (n + 2) -
              ccmActualHeadMatchedPolarCentroid (m + 2))) = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun m hm =>
        Finset.sum_nonneg fun n hn =>
          ccmActualHeadMatchedQuantileLorentzEdgeDissipation_nonneg m n)).mp hdiss
    unfold ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance
    apply Finset.sum_eq_zero
    rintro ⟨m, n⟩ hmn
    simp only [ccmActualHeadMatchedQuantileLorentzEdgeSet, Finset.mem_sigma] at hmn
    have hinner := (Finset.sum_eq_zero_iff_of_nonneg (fun n hn =>
      ccmActualHeadMatchedQuantileLorentzEdgeDissipation_nonneg m n)).mp
        (houter m hmn.1)
    have hd : ccmActualHeadMatchedQuantileLorentzEdgeDissipation m n = 0 := by
      simpa [ccmActualHeadMatchedQuantileLorentzEdgeDissipation] using hinner n hmn.2
    exact (ccmActualHeadMatchedQuantileLorentzEffectiveResistance_eq_zero_iff_dissipation_eq_zero
      (Ne.symm (Finset.mem_erase.mp hmn.2).1)).mpr hd

/-- The effective graph has exactly the existing active relative-offset radical. -/
theorem ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance_eq_zero_iff_active_displacement_constant
    (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance K = 0 ↔
      ∀ m n : Fin (K + 1),
        IsPrimePow ((m : ℕ) + 2) → IsPrimePow ((n : ℕ) + 2) →
          ccmActualHeadMatchedQuantilePolarDisplacement ((m : ℕ) + 2) =
            ccmActualHeadMatchedQuantilePolarDisplacement ((n : ℕ) + 2) := by
  rw [ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance_eq_zero_iff_graphDissipation_eq_zero,
    ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation_eq_zero_iff_active_displacement_constant]

/-!
The raw base-prime resistance lower bound is not itself an obstruction after exact null-edge
deletion.  The following local classification identifies exactly what survives: every active
vertex whose transport displacement differs from the base prime contributes its full critical
Mellin pair mass to effective resistance.  Thus a bounded effective wall would impose a concrete
weighted rigidity law on the literal transport, rather than merely a global quotient condition.
-/

private theorem ccmActualHeadQuantilePolarCentroid_succ_sub_eq_atomWeight_half_add_effective
    (n : ℕ) :
    ccmActualHeadQuantilePolarCentroid (n + 1) -
      ccmActualHeadQuantilePolarCentroid n =
        (criticalMellinAtomWeight n + criticalMellinAtomWeight (n + 1)) / 2 := by
  unfold ccmActualHeadQuantilePolarCentroid
  have h0 := ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight n
  have h1 := ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight (n + 1)
  linarith

private theorem ccmActualHeadQuantilePolarCentroid_lt_of_lt_of_isPrimePow_effective
    {m n : ℕ} (hmn : m < n) (hm : IsPrimePow m) :
    ccmActualHeadQuantilePolarCentroid m < ccmActualHeadQuantilePolarCentroid n := by
  have hstep : 0 < ccmActualHeadQuantilePolarCentroid (m + 1) -
      ccmActualHeadQuantilePolarCentroid m := by
    rw [ccmActualHeadQuantilePolarCentroid_succ_sub_eq_atomWeight_half_add_effective]
    have hpos : 0 < criticalMellinAtomWeight m := criticalMellinAtomWeight_pos hm
    have hnonneg : 0 ≤ criticalMellinAtomWeight (m + 1) :=
      criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _
    positivity
  have hmn' : m + 1 ≤ n := Nat.succ_le_iff.mpr hmn
  exact lt_of_lt_of_le (sub_pos.mp hstep)
    (ccmActualHeadQuantilePolarCentroid_le_of_le hmn')

/-- **Literal active-edge rigidity.** For two distinct prime-power vertices, singular
dissipation vanishes exactly when their matched--quantile transport displacements coincide. -/
theorem ccmActualHeadMatchedQuantileLorentzEdgeDissipation_eq_zero_iff_displacement_eq
    {m n : ℕ} (hmn : m ≠ n) (hm : IsPrimePow (m + 2)) (hn : IsPrimePow (n + 2)) :
    ccmActualHeadMatchedQuantileLorentzEdgeDissipation m n = 0 ↔
      ccmActualHeadMatchedQuantilePolarDisplacement (m + 2) =
        ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) := by
  let c : ℝ := ccmActualHeadMatchedPolarCentroid (n + 2) -
    ccmActualHeadMatchedPolarCentroid (m + 2)
  let q : ℝ := ccmActualHeadQuantilePolarCentroid (n + 2) -
    ccmActualHeadQuantilePolarCentroid (m + 2)
  let d : ℝ := ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
    ccmActualHeadMatchedQuantilePolarDisplacement (m + 2)
  have hcq : 0 < c * (c + q) := by
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · have hc : 0 < c := by
        dsimp [c]
        exact sub_pos.mpr
          (strictMono_ccmActualHeadMatchedPolarCentroid_shift_two (by omega))
      have hq : 0 < q := by
        dsimp [q]
        exact sub_pos.mpr
          (ccmActualHeadQuantilePolarCentroid_lt_of_lt_of_isPrimePow_effective
            (by omega) (by simpa using hm))
      positivity
    · have hc : c < 0 := by
        dsimp [c]
        exact sub_neg.mpr
          (strictMono_ccmActualHeadMatchedPolarCentroid_shift_two (by omega))
      have hq : q < 0 := by
        dsimp [q]
        exact sub_neg.mpr
          (ccmActualHeadQuantilePolarCentroid_lt_of_lt_of_isPrimePow_effective
            (by omega) (by simpa using hn))
      nlinarith
  have hw : 0 <
      (criticalMellinAtomWeight (m + 2) * criticalMellinAtomWeight (n + 2)) / 2 := by
    have hwm : 0 < criticalMellinAtomWeight (m + 2) := criticalMellinAtomWeight_pos hm
    have hwn : 0 < criticalMellinAtomWeight (n + 2) := criticalMellinAtomWeight_pos hn
    positivity
  have hfactor : 0 <
      (criticalMellinAtomWeight (m + 2) * criticalMellinAtomWeight (n + 2)) / 2 *
        (c * (c + q)) := mul_pos hw hcq
  have hformula : ccmActualHeadMatchedQuantileLorentzEdgeDissipation m n =
      ((criticalMellinAtomWeight (m + 2) * criticalMellinAtomWeight (n + 2)) / 2 *
        (c * (c + q))) * d ^ (2 : ℕ) := by
    unfold ccmActualHeadMatchedQuantileLorentzEdgeDissipation
      ccmActualHeadMatchedQuantileLorentzEdgeCurrent
    rw [ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_lorentzEdge]
    unfold ccmActualHeadMatchedQuantileLorentzSquare ccmActualHeadMatchedQuantileLorentzEdge
    simp
    dsimp [c, q, d]
    rw [ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement (m + 2),
      ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement (n + 2)]
    ring
  constructor
  · intro hzero
    rw [hformula] at hzero
    have hd2 : d ^ (2 : ℕ) = 0 := (mul_eq_zero.mp hzero).resolve_left hfactor.ne'
    have hd : d = 0 := sq_eq_zero_iff.mp hd2
    dsimp [d] at hd
    linarith
  · intro heq
    rw [hformula]
    have hd : d = 0 := by
      dsimp [d]
      linarith
    rw [hd]
    ring

/-- One active vertex displaced from the base prime contributes its full literal pair cost even
after all dissipation-null edges have been removed. -/
theorem ccmActualHeadMatchedQuantileLorentzEffectiveResistance_ge_base_weight_of_active_displacement_ne
    {n : ℕ} (hn0 : n ≠ 0) (hn : IsPrimePow (n + 2))
    (hdisp : ccmActualHeadMatchedQuantilePolarDisplacement 2 ≠
      ccmActualHeadMatchedQuantilePolarDisplacement (n + 2)) :
    criticalMellinAtomWeight 2 * criticalMellinAtomWeight (n + 2) / 2 ≤
      ccmActualHeadMatchedQuantileLorentzEffectiveResistance 0 n := by
  have hdiss : ccmActualHeadMatchedQuantileLorentzEdgeDissipation 0 n ≠ 0 := by
    intro hzero
    exact hdisp
      (ccmActualHeadMatchedQuantileLorentzEdgeDissipation_eq_zero_iff_displacement_eq
        (m := 0) (n := n) hn0.symm Nat.prime_two.isPrimePow hn |>.mp hzero)
  unfold ccmActualHeadMatchedQuantileLorentzEffectiveResistance
  rw [if_neg hdiss]
  exact ccmActualHeadMatchedQuantileLorentzEdgeResistance_ge_weight_product_half hn0.symm

/-- Local geometric endpoint channel retained by the literal matched-to-quantile transport. -/
def ccmActualHeadMatchedPolarUpperExcess (n : ℕ) : ℝ :=
  ccmActualHeadMatchedPolarUpperCoordinate n -
    2 * Real.exp (Real.log n / 2)

/-- **Source form of base-displacement coherence.** Equality of the literal transport
displacement with the base prime is exactly equality of the completed outgoing node error plus
its marked geometric endpoint channel. No sign, asymptotic, or RH premise is used. -/
theorem ccmActualHeadMatchedQuantilePolarDisplacement_eq_base_iff_outgoingNodeError_add_upperExcess_eq_base
    {n : ℕ} (hn : 0 < n) :
    ccmActualHeadMatchedQuantilePolarDisplacement n =
      ccmActualHeadMatchedQuantilePolarDisplacement 2 ↔
      ccmActualHeadOutgoingNodeError n + ccmActualHeadMatchedPolarUpperExcess n =
        ccmActualHeadOutgoingNodeError 2 + ccmActualHeadMatchedPolarUpperExcess 2 := by
  rw [ccmActualHeadMatchedQuantilePolarDisplacement_eq_neg_error_sub_upperExcess n hn,
    ccmActualHeadMatchedQuantilePolarDisplacement_eq_neg_error_sub_upperExcess 2 (by omega)]
  unfold ccmActualHeadMatchedPolarUpperExcess
  constructor <;> intro h <;> linarith

/-- Active prime-power vertices whose displacement differs from the base prime `2`. -/
def ccmActualHeadMatchedQuantileBaseDisplacementExceptionalVertices (K : ℕ) : Finset ℕ :=
  ((Finset.range (K + 1)).erase 0).filter fun n =>
    IsPrimePow (n + 2) ∧
      ccmActualHeadMatchedQuantilePolarDisplacement 2 ≠
        ccmActualHeadMatchedQuantilePolarDisplacement (n + 2)

/-- Critical-Mellin mass of the literal base-displacement exceptional vertices. -/
def ccmActualHeadMatchedQuantileBaseDisplacementExceptionalMass (K : ℕ) : ℝ :=
  ∑ n ∈ ccmActualHeadMatchedQuantileBaseDisplacementExceptionalVertices K,
    criticalMellinAtomWeight (n + 2)

/-- Literal prime-power vertices where completed outgoing error plus its retained endpoint
channel differs from the base-prime value. -/
def ccmActualHeadMatchedQuantileBaseCompletedTransportMismatchVertices (K : ℕ) : Finset ℕ :=
  ((Finset.range (K + 1)).erase 0).filter fun n =>
    IsPrimePow (n + 2) ∧
      ccmActualHeadOutgoingNodeError (n + 2) + ccmActualHeadMatchedPolarUpperExcess (n + 2) ≠
        ccmActualHeadOutgoingNodeError 2 + ccmActualHeadMatchedPolarUpperExcess 2

/-- The base-displacement exceptional set is literally the completed-source mismatch set. -/
theorem ccmActualHeadMatchedQuantileBaseDisplacementExceptionalVertices_eq_sourceMismatch
    (K : ℕ) :
    ccmActualHeadMatchedQuantileBaseDisplacementExceptionalVertices K =
      ccmActualHeadMatchedQuantileBaseCompletedTransportMismatchVertices K := by
  ext n
  have hiff :
      ccmActualHeadMatchedQuantilePolarDisplacement 2 =
        ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) ↔
      ccmActualHeadOutgoingNodeError (n + 2) + ccmActualHeadMatchedPolarUpperExcess (n + 2) =
        ccmActualHeadOutgoingNodeError 2 + ccmActualHeadMatchedPolarUpperExcess 2 := by
    constructor
    · intro h
      exact
        (ccmActualHeadMatchedQuantilePolarDisplacement_eq_base_iff_outgoingNodeError_add_upperExcess_eq_base
          (n := n + 2) (by omega)).mp h.symm
    · intro h
      exact
        (ccmActualHeadMatchedQuantilePolarDisplacement_eq_base_iff_outgoingNodeError_add_upperExcess_eq_base
          (n := n + 2) (by omega)).mpr h |>.symm
  simp only [ccmActualHeadMatchedQuantileBaseDisplacementExceptionalVertices,
    ccmActualHeadMatchedQuantileBaseCompletedTransportMismatchVertices,
    Finset.mem_filter, Finset.mem_erase, Finset.mem_range]
  constructor
  · rintro ⟨hindex, hactive, hne⟩
    exact ⟨hindex, hactive, fun hsource => hne (hiff.mpr hsource)⟩
  · rintro ⟨hindex, hactive, hne⟩
    exact ⟨hindex, hactive, fun hdisp => hne (hiff.mp hdisp)⟩

/-- Critical-Mellin mass of literal completed-transport mismatches from the base prime. -/
def ccmActualHeadMatchedQuantileBaseCompletedTransportMismatchMass (K : ℕ) : ℝ :=
  ∑ n ∈ ccmActualHeadMatchedQuantileBaseCompletedTransportMismatchVertices K,
    criticalMellinAtomWeight (n + 2)

/-- Displacement-exception mass is exactly the completed-source mismatch mass. -/
theorem ccmActualHeadMatchedQuantileBaseDisplacementExceptionalMass_eq_sourceMismatch
    (K : ℕ) :
    ccmActualHeadMatchedQuantileBaseDisplacementExceptionalMass K =
      ccmActualHeadMatchedQuantileBaseCompletedTransportMismatchMass K := by
  unfold ccmActualHeadMatchedQuantileBaseDisplacementExceptionalMass
    ccmActualHeadMatchedQuantileBaseCompletedTransportMismatchMass
  rw [ccmActualHeadMatchedQuantileBaseDisplacementExceptionalVertices_eq_sourceMismatch]

/-- **Effective-resistance rigidity envelope.** A finite-head effective resistance bound forces
the same bound on all prime-power mass whose literal displacement differs from the base prime.
This identifies the exact exceptional set which any cofinal effective wall must control. -/
theorem ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance_ge_baseExceptionalMass
    (K : ℕ) :
    (criticalMellinAtomWeight 2 / 2) *
        ccmActualHeadMatchedQuantileBaseDisplacementExceptionalMass K ≤
      ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance K := by
  let s : Finset ℕ := (Finset.range (K + 1)).erase 0
  let p : ℕ → Prop := fun n => IsPrimePow (n + 2) ∧
    ccmActualHeadMatchedQuantilePolarDisplacement 2 ≠
      ccmActualHeadMatchedQuantilePolarDisplacement (n + 2)
  have hlocal : ∀ n ∈ s.filter p,
      criticalMellinAtomWeight 2 * criticalMellinAtomWeight (n + 2) / 2 ≤
        ccmActualHeadMatchedQuantileLorentzEffectiveResistance 0 n := by
    intro n hn
    have hns : n ∈ s := (Finset.mem_filter.mp hn).1
    have hnp : p n := (Finset.mem_filter.mp hn).2
    exact ccmActualHeadMatchedQuantileLorentzEffectiveResistance_ge_base_weight_of_active_displacement_ne
      (Finset.mem_erase.mp hns).1 hnp.1 hnp.2
  have hbase :
      (criticalMellinAtomWeight 2 / 2) *
          ccmActualHeadMatchedQuantileBaseDisplacementExceptionalMass K =
        ∑ n ∈ s.filter p,
          criticalMellinAtomWeight 2 * criticalMellinAtomWeight (n + 2) / 2 := by
    unfold ccmActualHeadMatchedQuantileBaseDisplacementExceptionalMass
      ccmActualHeadMatchedQuantileBaseDisplacementExceptionalVertices
    dsimp [s, p]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hbase]
  calc
    (∑ n ∈ s.filter p,
        criticalMellinAtomWeight 2 * criticalMellinAtomWeight (n + 2) / 2) ≤
      ∑ n ∈ s.filter p, ccmActualHeadMatchedQuantileLorentzEffectiveResistance 0 n := by
        exact Finset.sum_le_sum fun n hn => hlocal n hn
    _ ≤ ∑ n ∈ s, ccmActualHeadMatchedQuantileLorentzEffectiveResistance 0 n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset p s)
        intro n hn hnot
        exact ccmActualHeadMatchedQuantileLorentzEffectiveResistance_nonneg
          (Ne.symm (Finset.mem_erase.mp hn).1)
    _ ≤ ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance K := by
        have houter :
            (∑ n ∈ (Finset.range (K + 1)).erase 0,
              ccmActualHeadMatchedQuantileLorentzEffectiveResistance 0 n) ≤
            ∑ m ∈ Finset.range (K + 1),
              ∑ n ∈ (Finset.range (K + 1)).erase m,
                ccmActualHeadMatchedQuantileLorentzEffectiveResistance m n := by
          exact Finset.single_le_sum
            (s := Finset.range (K + 1))
            (f := fun m => ∑ n ∈ (Finset.range (K + 1)).erase m,
              ccmActualHeadMatchedQuantileLorentzEffectiveResistance m n)
            (fun m hm => Finset.sum_nonneg fun n hn =>
              ccmActualHeadMatchedQuantileLorentzEffectiveResistance_nonneg
                (Ne.symm (Finset.mem_erase.mp hn).1))
            (Finset.mem_range.mpr (Nat.succ_pos K))
        simpa [s, ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance,
          ccmActualHeadMatchedQuantileLorentzEdgeSet, Finset.sum_sigma] using houter

/-- **Direct completed-source lower envelope.** Any finite effective graph wall must pay at
least the critical-Mellin mass of every prime-power node where the completed error plus retained
endpoint channel differs from its base-prime value. -/
theorem ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance_ge_baseSourceMismatchMass
    (K : ℕ) :
    (criticalMellinAtomWeight 2 / 2) *
        ccmActualHeadMatchedQuantileBaseCompletedTransportMismatchMass K ≤
      ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance K := by
  rw [← ccmActualHeadMatchedQuantileBaseDisplacementExceptionalMass_eq_sourceMismatch]
  exact ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance_ge_baseExceptionalMass K

end RHTower
