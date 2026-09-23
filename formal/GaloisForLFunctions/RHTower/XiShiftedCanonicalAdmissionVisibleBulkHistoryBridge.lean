import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionGaussBulkLowEdgeFloor
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionNondegenerateSourceEffectivity
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdjacentHistoryBudget

/-!
# Literal bridge from Gaussian-visible bulk to adjacent source history

The degree-uniform Route U bulk floor is Gaussian-visible, while Route U's literal budget is
paid by completed arithmetic source on adjacent degree edges.  This file supplies the missing
finite-block conversion without altering either object: after multiplication by the next
admission norm, current Gaussian bulk is paid by the next literal adjacent source supply.

The remaining Route U obstruction is therefore not a missing bulk-to-history conversion.  It is
the genuinely asymptotic question of controlling the product of consecutive admission norms in
the exact source normalization.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

/-- On every finite positive moment block, Gaussian-visible Jacobi energy is bounded by the
following completed source history with the exact existing quadratic effectivity weight. -/
theorem adaptiveOrthoVisibleJacobiEnergy_le_effectivityWeight_mul_nextNondegenerateHistory
    {s : ℕ → ℝ} {N n : ℕ}
    (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 1 ≤ n) (hnN : n + 2 ≤ N) :
    HTGeometry.adaptiveOrthoJacobiEnergy s n -
        (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s (n + 1) ≤
      xiShiftedNondegenerateSourceEffectivityWeight n *
        HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory s (n + 1) := by
  let a : ℝ := HTGeometry.monicOrthoAlpha s n
  let A : ℝ := ∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ)
  let B : ℝ := ∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j
  let b : ℝ := HTGeometry.monicOrthoBeta s n
  let K : ℝ := xiShiftedNondegenerateSourceEffectivityWeight n
  have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB : 0 ≤ B := by
    dsimp [B]
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below h (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  have hb : 0 ≤ b := by
    dsimp [b]
    exact (HTGeometry.monicOrthoBeta_pos_below h (by omega) (by omega)).le
  have hK : 0 ≤ K := by
    dsimp [K, xiShiftedNondegenerateSourceEffectivityWeight]
    positivity
  have hKtwo : 2 ≤ K := by
    dsimp [K, xiShiftedNondegenerateSourceEffectivityWeight]
    nlinarith [sq_nonneg (2 * (n : ℝ) + 1)]
  have hKalpha : 3 * (n : ℝ) / 2 + 1 ≤ K := by
    dsimp [K, xiShiftedNondegenerateSourceEffectivityWeight]
    nlinarith [sq_nonneg (n : ℝ)]
  have hKbeta : (n : ℝ) + 1 ≤ 2 * K := by
    dsimp [K, xiShiftedNondegenerateSourceEffectivityWeight]
    nlinarith [sq_nonneg (n : ℝ)]
  have hcross (j : ℕ) :
      (HTGeometry.monicOrthoAlpha s j + a / 2) ^ (2 : ℕ) ≤
        2 * HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ) + a ^ (2 : ℕ) / 2 := by
    nlinarith [sq_nonneg (HTGeometry.monicOrthoAlpha s j - a / 2)]
  have hsumCross :
      (∑ j ∈ Finset.range n,
        (HTGeometry.monicOrthoAlpha s j + a / 2) ^ (2 : ℕ)) ≤
        2 * A + (n : ℝ) * a ^ (2 : ℕ) / 2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range n,
          (2 * HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ) + a ^ (2 : ℕ) / 2) := by
        apply Finset.sum_le_sum
        intro j _
        exact hcross j
      _ = 2 * A + (n : ℝ) * a ^ (2 : ℕ) / 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  have hhistoryLower :
      A + a ^ (2 : ℕ) + 2 * B + 2 * b ≤
        HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory s (n + 1) := by
    unfold HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    dsimp [A, B, a, b]
    nlinarith [sq_nonneg (HTGeometry.monicOrthoFirstCoeff s (n + 1)),
      sq_nonneg (HTGeometry.monicOrthoAlpha s (n + 1))]
  have hleft :
      HTGeometry.adaptiveOrthoJacobiEnergy s n -
          (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s (n + 1) ≤
        2 * A + (3 * (n : ℝ) / 2 + 1) * a ^ (2 : ℕ) + 2 * B +
          ((n : ℝ) + 1) * b := by
    unfold HTGeometry.adaptiveOrthoJacobiEnergy
    dsimp [a, A, B, b] at hsumCross ⊢
    nlinarith
  have hAcoeff : 2 * A ≤ K * A := by
    exact mul_le_mul_of_nonneg_right hKtwo hA
  have hacoeff : (3 * (n : ℝ) / 2 + 1) * a ^ (2 : ℕ) ≤ K * a ^ (2 : ℕ) := by
    exact mul_le_mul_of_nonneg_right hKalpha (sq_nonneg a)
  have hBcoeff : 2 * B ≤ K * (2 * B) := by
    have htwoK : 2 ≤ 2 * K := by linarith
    calc
      2 * B ≤ (2 * K) * B := mul_le_mul_of_nonneg_right htwoK hB
      _ = K * (2 * B) := by ring
  have hbcoeff : ((n : ℝ) + 1) * b ≤ K * (2 * b) := by
    calc
      ((n : ℝ) + 1) * b ≤ (2 * K) * b :=
        mul_le_mul_of_nonneg_right hKbeta hb
      _ = K * (2 * b) := by ring
  have hweighted :
      2 * A + (3 * (n : ℝ) / 2 + 1) * a ^ (2 : ℕ) + 2 * B +
          ((n : ℝ) + 1) * b ≤
        K * (A + a ^ (2 : ℕ) + 2 * B + 2 * b) := by
    calc
      _ ≤ K * A + K * a ^ (2 : ℕ) + K * (2 * B) + K * (2 * b) := by
        linarith
      _ = _ := by ring
  calc
    HTGeometry.adaptiveOrthoJacobiEnergy s n -
        (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s (n + 1) ≤
      2 * A + (3 * (n : ℝ) / 2 + 1) * a ^ (2 : ℕ) + 2 * B +
          ((n : ℝ) + 1) * b := hleft
    _ ≤ K * (A + a ^ (2 : ℕ) + 2 * B + 2 * b) := hweighted
    _ ≤ K *
        HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory s (n + 1) :=
      mul_le_mul_of_nonneg_left hhistoryLower hK

/-- **Literal Route U bulk-to-history bridge.**  On every actual positive Hankel block, next
admission norm times current source-selected Gaussian bulk is paid by the literal adjacent
completed arithmetic source supply on the next degree edge. -/
theorem nextAdmissionNorm_mul_adaptiveGaussBulk_le_nextAdjacentLiteralSourceSupply
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 1 ≤ n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef) :
    xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) *
        xiShiftedAdaptiveGaussArithmeticBulk w n ≤
      routeUAdjacentLiteralSourceSupply w (n + 1) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re
  have hseq : s = xiShiftedRealMomentSequence w := rfl
  have hH' : (HTGeometry.momentHankelMatrix s (n + 3)).PosDef := by
    rw [hseq]
    exact hH
  let K : ℝ := xiShiftedNondegenerateSourceEffectivityWeight n
  have hsmall : (HTGeometry.momentHankelMatrix s (n + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH'
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH'
  have hvisible :=
    adaptiveOrthoVisibleJacobiEnergy_le_effectivityWeight_mul_nextNondegenerateHistory
      hbelow hn (by omega : n + 2 ≤ n + 3)
  have hnormN : 0 ≤ xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hsmall]
    exact (HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hsmall) (by omega)).le
  have hnormNext : 0 ≤ xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH']
    exact (HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)).le
  have hsourceNext :
      xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass (w ^ (2 : ℕ)) (n + 1) =
        2 * xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) *
          HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory s
            (n + 1) := by
    simpa only [s] using
      xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass_eq_norm_mul_history
        (y := w ^ (2 : ℕ)) (n := n + 1) (by omega) hH'
  have hgauss :
      xiShiftedAdaptiveGaussArithmeticBulk w n =
        2 * xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
          (HTGeometry.adaptiveOrthoJacobiEnergy s n -
            (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s (n + 1)) := by
    rw [xiShiftedAdaptiveGaussArithmeticBulk,
      ← hseq,
      HTGeometry.adaptiveOrthoGaussAggregate_eq_visibleJacobiEnergy
        (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hsmall) (by omega)
        (by omega : n + 2 ≤ n + 2),
      xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hsmall]
    simp only [s]
    ring
  have hbulkSource :
      xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) *
          xiShiftedAdaptiveGaussArithmeticBulk w n ≤
        K * xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
          xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass (w ^ (2 : ℕ)) (n + 1) := by
    rw [hgauss, hsourceNext]
    have hscaled := mul_le_mul_of_nonneg_left hvisible
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg hnormN hnormNext))
    nlinarith
  have hKmono : K ≤ xiShiftedNondegenerateSourceEffectivityWeight (n + 1) := by
    have hdiff : xiShiftedNondegenerateSourceEffectivityWeight (n + 1) - K =
        8 * (n : ℝ) + 8 := by
      dsimp [K, xiShiftedNondegenerateSourceEffectivityWeight]
      push_cast
      ring
    nlinarith
  have hsourcePos : 0 ≤
      xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass (w ^ (2 : ℕ)) (n + 1) := by
    rw [hsourceNext]
    have hhistory : 0 ≤
        HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory s (n + 1) :=
      le_trans zero_le_one
        (one_le_nondegenerateNullFlagCompletedJacobiHistory hbelow (by omega))
    exact mul_nonneg (mul_nonneg (by norm_num) hnormNext) hhistory
  have hfirst :
      K * xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
          xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass (w ^ (2 : ℕ)) (n + 1) ≤
        xiShiftedNondegenerateSourceEffectivityWeight (n + 1) *
          xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
          xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass (w ^ (2 : ℕ)) (n + 1) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKmono hnormN) hsourcePos
  have hsecond : 0 ≤
      xiShiftedNondegenerateSourceEffectivityWeight n *
        xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) *
        xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass (w ^ (2 : ℕ)) n := by
    have hsource : 0 ≤ xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass (w ^ (2 : ℕ)) n := by
      rw [xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass_eq_norm_mul_history
        (y := w ^ (2 : ℕ)) (n := n) (by omega) hsmall]
      have hhistory : 0 ≤
          HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory s n :=
        le_trans zero_le_one
          (one_le_nondegenerateNullFlagCompletedJacobiHistory
            (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hsmall) (by omega))
      exact mul_nonneg (mul_nonneg (by norm_num) hnormN) hhistory
    have hweight : 0 ≤ xiShiftedNondegenerateSourceEffectivityWeight n := by
      unfold xiShiftedNondegenerateSourceEffectivityWeight
      positivity
    exact mul_nonneg (mul_nonneg hweight hnormNext) hsource
  calc
    xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) *
        xiShiftedAdaptiveGaussArithmeticBulk w n ≤
      K * xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
          xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass (w ^ (2 : ℕ)) (n + 1) :=
      hbulkSource
    _ ≤ xiShiftedNondegenerateSourceEffectivityWeight (n + 1) *
          xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
          xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass (w ^ (2 : ℕ)) (n + 1) := hfirst
    _ ≤ xiShiftedNondegenerateSourceEffectivityWeight (n + 1) *
          xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
          xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass (w ^ (2 : ℕ)) (n + 1) +
        xiShiftedNondegenerateSourceEffectivityWeight n *
          xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) *
          xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass (w ^ (2 : ℕ)) n :=
      le_add_of_nonneg_right hsecond
    _ = routeUAdjacentLiteralSourceSupply w (n + 1) := by
      unfold routeUAdjacentLiteralSourceSupply
      rw [xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass_sq_eq_arithmetic hw
        (n + 1),
        xiShiftedCanonicalNondegenerateNullFlagCompletedSourceMass_sq_eq_arithmetic hw n]
      simp only [Nat.add_sub_cancel]

end

namespace XiShiftedCanonicalAdmission

/-- Exact reciprocal-mass transport of the completed-square Gaussian-visible bulk.  The
completed square, rather than an unshifted alpha-square surrogate, is transported termwise. -/
theorem relativeArithmeticGaussBulk_eq_fourth_mul_actualVisibleEnergy
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 0 < n)
    (hA : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 4)).PosDef) :
    relativeArithmeticGaussBulk w n =
      w ^ (4 : ℕ) *
        (HTGeometry.adaptiveOrthoJacobiEnergy (xiShiftedRealMomentSequence w) n -
          (n + 1 : ℝ) * HTGeometry.monicOrthoBeta
            (xiShiftedRealMomentSequence w) (n + 1)) := by
  have hN0 := xiShiftedFarRightNormalizedHankelMatrix_posDef_of_actual hw (n + 4) hA
  have hN : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 4)).PosDef := by
    simpa only [xiShiftedFarRightNormalizedHankelMatrix] using hN0
  have hNvisible : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef :=
    momentHankel_posDef_of_le (by omega) hN
  have hA' : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 4)).PosDef := hA
  have halpha : ∀ j, j ≤ n →
      HTGeometry.monicOrthoAlpha (xiShiftedFarRightNormalizedMoment w) j =
        w ^ (2 : ℕ) * HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) j := by
    intro j hj
    have hNj : (HTGeometry.momentHankelMatrix
        (xiShiftedFarRightNormalizedMoment w) (j + 3)).PosDef :=
      momentHankel_posDef_of_le (by omega) hN
    have hAj : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (j + 3)).PosDef :=
      momentHankel_posDef_of_le (by omega) hA'
    change HTGeometry.monicOrthoAlpha (xiShiftedFarRightNormalizedMoment w) j =
      w ^ (2 : ℕ) * HTGeometry.monicOrthoAlpha
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) j
    exact normalizedAlpha_eq_square_mul_actualAlpha hw j hNj hAj
  have hbeta : ∀ j, j ≤ n + 1 →
      HTGeometry.monicOrthoBeta (xiShiftedFarRightNormalizedMoment w) j =
        w ^ (4 : ℕ) * HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) j := by
    intro j hj
    have hNj : (HTGeometry.momentHankelMatrix
        (xiShiftedFarRightNormalizedMoment w) (j + 3)).PosDef :=
      momentHankel_posDef_of_le (by omega) hN
    have hAj : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (j + 3)).PosDef :=
      momentHankel_posDef_of_le (by omega) hA'
    change HTGeometry.monicOrthoBeta (xiShiftedFarRightNormalizedMoment w) j =
      w ^ (4 : ℕ) * HTGeometry.monicOrthoBeta
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) j
    exact normalizedBeta_eq_fourth_mul_actualBeta hw j hNj hAj
  have hsumShiftedAlpha :
      (∑ j ∈ Finset.range n,
        (HTGeometry.monicOrthoAlpha (xiShiftedFarRightNormalizedMoment w) j +
          HTGeometry.monicOrthoAlpha (xiShiftedFarRightNormalizedMoment w) n / 2) ^ (2 : ℕ)) =
      w ^ (4 : ℕ) * ∑ j ∈ Finset.range n,
        (HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) j +
          HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) n / 2) ^ (2 : ℕ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [halpha j (Finset.mem_range.mp hj).le, halpha n le_rfl]
    ring
  have hsumBeta :
      (∑ j ∈ Finset.range n,
        HTGeometry.monicOrthoBeta (xiShiftedFarRightNormalizedMoment w) j) =
      w ^ (4 : ℕ) * ∑ j ∈ Finset.range n,
        HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hbeta j ((Finset.mem_range.mp hj).le.trans (by omega))]
  rw [relativeArithmeticGaussBulk_eq_visibleEnergy hw hn hNvisible]
  unfold HTGeometry.adaptiveOrthoJacobiEnergy
  rw [hsumShiftedAlpha, hsumBeta, halpha n le_rfl,
    hbeta n (by omega), hbeta (n + 1) le_rfl]
  ring

/-- Exact gauge law for canonical admission norm.  The apparent raw norm collapse is entirely
the product of mass dilation and normalized moment-density factors. -/
theorem normalizedAdmissionNorm_eq_massGauge_mul_actualCanonicalNorm
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 0 < n)
    (hA : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    normalizedAdmissionNorm w n =
      (2 * w / Real.log w) * w ^ (4 * n) *
        xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n := by
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
  have hN0 := xiShiftedFarRightNormalizedHankelMatrix_posDef_of_actual hw (n + 2) hA
  have hN : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef := by
    simpa only [xiShiftedFarRightNormalizedHankelMatrix] using hN0
  have hNhead : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) n).PosDef :=
    momentHankel_posDef_of_le (by omega) hN
  have hAhead : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n).PosDef :=
    momentHankel_posDef_of_le (by omega) hA
  have hsource := sourceCoordinateAdmission_eq_actualAdmission hw hn
    (ne_of_gt hNhead.det_pos) (ne_of_gt hAhead.det_pos)
  have hactual : xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n =
      HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re)
        ((sourceCoordinateAdmission w n) ^ (2 : ℕ)) := by
    rw [xiShiftedCanonicalAdmissionNorm, HTGeometry.momentInner_self, ← hsource]
  have hsquare :
      ((dimensionlessAdmission w n) ^ (2 : ℕ)).comp (Polynomial.C (w ^ (2 : ℕ)) * Polynomial.X) =
        w ^ (4 * n) • (sourceCoordinateAdmission w n) ^ (2 : ℕ) := by
    rw [sourceCoordinateAdmission, smul_pow, ← mul_smul]
    have hpow : w ^ (4 * n) * ((w ^ (2 * n))⁻¹) ^ (2 : ℕ) = 1 := by
      have hfour : w ^ (4 * n) = (w ^ (2 * n)) ^ (2 : ℕ) := by
        calc
          w ^ (4 * n) = w ^ ((2 * n) * 2) := by
            congr 1
            omega
          _ = (w ^ (2 * n)) ^ (2 : ℕ) := by rw [pow_mul]
      rw [hfour]
      field_simp [pow_ne_zero _ hw0]
    rw [hpow, one_smul, Polynomial.pow_comp]
  rw [normalizedAdmissionNorm,
    momentFunctional_normalized_eq_massDilation hw ((dimensionlessAdmission w n) ^ (2 : ℕ)),
    hsquare, HTGeometry.momentFunctional_smul, ← hactual]
  ring

/-- Source-native transport of normalized relative Gaussian bulk to next literal adjacent
supply.  It retains both consecutive admission norms and exact fourth mass weight. -/
theorem two_mul_admissionNorm_product_mul_relativeArithmeticGaussBulk_le_fourth_mul_nextSupply
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 1 ≤ n)
    (hA : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 4)).PosDef) :
    2 * xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
        xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) *
        relativeArithmeticGaussBulk w n ≤
      w ^ (4 : ℕ) * routeUAdjacentLiteralSourceSupply w (n + 1) := by
  have hAthree : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef :=
    momentHankel_posDef_of_le (by omega) hA
  have hAtwo : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef :=
    momentHankel_posDef_of_le (by omega) hA
  have hbridge := RHTower.nextAdmissionNorm_mul_adaptiveGaussBulk_le_nextAdjacentLiteralSourceSupply
    (by linarith : 1 / 2 < w) hn hAthree
  have hscale := relativeArithmeticGaussBulk_eq_fourth_mul_actualVisibleEnergy hw
    (by omega : 0 < n) hA
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re
  have hseq : s = xiShiftedRealMomentSequence w := rfl
  have hAtwo' : (HTGeometry.momentHankelMatrix s (n + 2)).PosDef := by
    rw [hseq]
    exact hAtwo
  have hbulk : xiShiftedAdaptiveGaussArithmeticBulk w n =
      2 * xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
        (HTGeometry.adaptiveOrthoJacobiEnergy (xiShiftedRealMomentSequence w) n -
          (n + 1 : ℝ) * HTGeometry.monicOrthoBeta
            (xiShiftedRealMomentSequence w) (n + 1)) := by
    rw [xiShiftedAdaptiveGaussArithmeticBulk, ← hseq,
      HTGeometry.adaptiveOrthoGaussAggregate_eq_visibleJacobiEnergy
        (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hAtwo') (by omega)
        (by omega : n + 2 ≤ n + 2),
      xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hAtwo']
    simp only [s]
    ring
  calc
    2 * xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
        xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) *
        relativeArithmeticGaussBulk w n =
      w ^ (4 : ℕ) *
        (xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) *
          xiShiftedAdaptiveGaussArithmeticBulk w n) := by
        rw [hscale, hbulk]
        ring
    _ ≤ w ^ (4 : ℕ) * routeUAdjacentLiteralSourceSupply w (n + 1) :=
      mul_le_mul_of_nonneg_left hbridge (by positivity)

/-- **Uniform Route U consequence.**  The existing normalized `1/8` bulk floor forces a
strict lower bound for literal adjacent arithmetic source supply on every far-right positive
block.  The theorem identifies the sole retained degree factor: the product of consecutive
canonical admission norms. -/
theorem exists_uniform_admissionNormProduct_quarter_lt_fourth_mul_nextSupply :
    ∃ W : ℝ, ∀ w ≥ W, ∀ n : ℕ, 2 ≤ n →
      (HTGeometry.momentHankelMatrix
        (xiShiftedRealMomentSequence w) (n + 4)).PosDef →
      xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
          xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) / 4 <
        w ^ (4 : ℕ) * routeUAdjacentLiteralSourceSupply w (n + 1) := by
  obtain ⟨W, hW⟩ := exists_uniform_relativeArithmeticGaussBulk_eighth_of_actual
  refine ⟨max W 2, ?_⟩
  intro w hw n hn hA
  have hAtwo : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef :=
    momentHankel_posDef_of_le (by omega) hA
  have hAthree : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef :=
    momentHankel_posDef_of_le (by omega) hA
  have hwW : W ≤ w := le_trans (le_max_left _ _) hw
  have hwOne : 1 < w := lt_of_lt_of_le (by norm_num)
    (le_trans (le_max_right _ _) hw)
  have hfloor := hW w hwW n hn hAtwo
  have htransport :=
    two_mul_admissionNorm_product_mul_relativeArithmeticGaussBulk_le_fourth_mul_nextSupply
      hwOne (by omega) hA
  have hnorm : 0 < xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hAtwo]
    exact HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hAtwo) (by omega)
  have hnormNext : 0 < xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hAthree]
    exact HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hAthree) (by omega)
  have hprod : 0 < xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
      xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) := mul_pos hnorm hnormNext
  have hscaledFloor := mul_lt_mul_of_pos_left hfloor hprod
  have hstrict : xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
      xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) / 4 <
      2 * xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
        xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) *
        relativeArithmeticGaussBulk w n := by
    calc
      xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
          xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) / 4 =
        2 * (xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
          xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) * (1 / 8 : ℝ)) := by ring
      _ < 2 * (xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
          xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) *
          relativeArithmeticGaussBulk w n) :=
        mul_lt_mul_of_pos_left hscaledFloor (by norm_num)
      _ = _ := by ring
  exact hstrict.trans_le htransport

/-- **Gauge-normalized Route U consequence.**  Raw admission-norm collapse cancels exactly
against mass dilation.  The literal source lower bound is therefore nontrivial in the normalized
coordinates in which the source recession is defined. -/
theorem exists_uniform_logSq_mul_normalizedNormProduct_lt_massScaled_nextSupply :
    ∃ W : ℝ, ∀ w ≥ W, ∀ n : ℕ, 2 ≤ n →
      (HTGeometry.momentHankelMatrix
        (xiShiftedRealMomentSequence w) (n + 4)).PosDef →
      Real.log w ^ (2 : ℕ) * normalizedAdmissionNorm w n * normalizedAdmissionNorm w (n + 1) <
        16 * w ^ (8 * n + 10) * routeUAdjacentLiteralSourceSupply w (n + 1) := by
  obtain ⟨W, hW⟩ := exists_uniform_admissionNormProduct_quarter_lt_fourth_mul_nextSupply
  refine ⟨max W 2, ?_⟩
  intro w hw n hn hA
  have hwW : W ≤ w := le_trans (le_max_left _ _) hw
  have hwOne : 1 < w := lt_of_lt_of_le (by norm_num)
    (le_trans (le_max_right _ _) hw)
  have hAtwo : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef :=
    momentHankel_posDef_of_le (by omega) hA
  have hAthree : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) ((n + 1) + 2)).PosDef :=
    momentHankel_posDef_of_le (by omega) hA
  have hraw := hW w hwW n hn hA
  have hnorm := normalizedAdmissionNorm_eq_massGauge_mul_actualCanonicalNorm
    hwOne (by omega) hAtwo
  have hnormNext := normalizedAdmissionNorm_eq_massGauge_mul_actualCanonicalNorm
    hwOne (by omega) hAthree
  let K : ℝ := 16 * w ^ (8 * n + 6)
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  have hscaled := mul_lt_mul_of_pos_left hraw hKpos
  have hnextPow : w ^ (4 * (n + 1)) = w ^ (4 * n) * w ^ (4 : ℕ) := by
    calc
      w ^ (4 * (n + 1)) = w ^ (4 * n + 4) := by
        congr 1
      _ = w ^ (4 * n) * w ^ (4 : ℕ) := by rw [pow_add]
  have hsourcePow : w ^ (8 * n + 10) = w ^ (8 * n + 6) * w ^ (4 : ℕ) := by
    calc
      w ^ (8 * n + 10) = w ^ ((8 * n + 6) + 4) := by
        congr 1
      _ = w ^ (8 * n + 6) * w ^ (4 : ℕ) := by rw [pow_add]
  rw [hnorm, hnormNext, hnextPow]
  have hlog : Real.log w ≠ 0 := ne_of_gt (Real.log_pos hwOne)
  have hcancel : Real.log w ^ (2 : ℕ) * (2 * w / Real.log w) *
      (2 * w / Real.log w) = 4 * w ^ (2 : ℕ) := by
    field_simp [hlog]
    ring
  have hpower : w ^ (2 : ℕ) * w ^ (4 * n) * w ^ (4 * n) * w ^ (4 : ℕ) =
      w ^ (8 * n + 6) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  have hleft : Real.log w ^ (2 : ℕ) *
      ((2 * w / Real.log w) * w ^ (4 * n) * xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n) *
      ((2 * w / Real.log w) * (w ^ (4 * n) * w ^ (4 : ℕ)) *
        xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1)) =
      K * (xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
        xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) / 4) := by
    dsimp [K]
    calc
      _ = (Real.log w ^ (2 : ℕ) * (2 * w / Real.log w) * (2 * w / Real.log w)) *
          (w ^ (4 * n) * w ^ (4 * n) * w ^ (4 : ℕ)) *
          (xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
            xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1)) := by ring
      _ = 4 * (w ^ (2 : ℕ) * w ^ (4 * n) * w ^ (4 * n) * w ^ (4 : ℕ)) *
          (xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
            xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1)) := by
        rw [hcancel]
        ring
      _ = _ := by rw [hpower]; ring
  calc
    Real.log w ^ (2 : ℕ) *
        ((2 * w / Real.log w) * w ^ (4 * n) * xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n) *
        ((2 * w / Real.log w) * (w ^ (4 * n) * w ^ (4 : ℕ)) *
          xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1)) =
      K * (xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) n *
        xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) / 4) := hleft
    _ < K * (w ^ (4 : ℕ) * routeUAdjacentLiteralSourceSupply w (n + 1)) := hscaled
    _ = 16 * w ^ (8 * n + 10) * routeUAdjacentLiteralSourceSupply w (n + 1) := by
      dsimp [K]
      rw [hsourcePow]
      ring

end XiShiftedCanonicalAdmission

end RHTower
