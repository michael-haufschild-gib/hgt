import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualODEClosure

/-!
# Two-sided Abel closure of the Route-T residual source

The left endpoint Abel variation is the exact absolute-convergence norm of the residual Hardy
source.  Its right endpoint translate contains the missing mesh information.  Together they form
one graph norm:

`sum (|R_N| + |R_{N+1}|) * delta_N * exp (h_N / 2) < infinity`.

The residual recurrence `delta_N = w_{N+1} + R_N - R_{N+1}` then forces the critical logarithmic
cell square.  The Wold term is harmless by exponential-potential telescoping.  Consequently the
two-sided graph norm supplies both inputs of the Route-T ODE closure: left variation opens the
residual source half-strip, while the translated variation forces critical prime-gap mesh energy.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- Right-endpoint translate of the residual upper Abel variation. -/
def xiHeatCassiniWoldResidualRightUpperVariationAtom (a : ℝ) (N : ℕ) : ℝ :=
  |xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1)| *
    xiHeatCassiniOrderedPrimeLogGap N *
      Real.exp (a * xiMassNthPrimeLogHeight N)

theorem xiHeatCassiniWoldResidualRightUpperVariationAtom_nonneg
    (a : ℝ) (N : ℕ) :
    0 ≤ xiHeatCassiniWoldResidualRightUpperVariationAtom a N := by
  exact mul_nonneg
    (mul_nonneg (abs_nonneg _)
      (xiHeatCassiniOrderedPrimeLogGap_nonneg N))
    (Real.exp_nonneg _)

/-- The local Wold mass paired with one logarithmic cell is summable at critical half-density.
This is the lower-order term in the residual recurrence. -/
theorem summable_woldCoeff_mul_primeLogGap_mul_criticalHalfDensity :
    Summable (fun N : ℕ =>
      woldCoeff 1 (nthPrimeSubtype (N + 1)) *
        xiHeatCassiniOrderedPrimeLogGap N *
          Real.exp (xiMassNthPrimeLogHeight N / 2)) := by
  have hheight :=
    summable_primeLogGap_mul_height_mul_exp_neg_height
      (show (0 : ℝ) < 1 / 2 by norm_num)
  have hcell :=
    summable_primeLogGap_mul_exp_neg_height
      (show (0 : ℝ) < 1 / 2 by norm_num)
  have hmajor := hheight.add hcell
  refine Summable.of_nonneg_of_le (fun N => ?_) (fun N => ?_) hmajor
  · exact mul_nonneg
      (mul_nonneg (woldCoeff_nonneg 1 _)
        (xiHeatCassiniOrderedPrimeLogGap_nonneg N))
      (Real.exp_nonneg _)
  · let h : ℝ := xiMassNthPrimeLogHeight N
    let y : ℝ := xiMassNthPrimeLogHeight (N + 1)
    let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
    have hh : 0 < h := xiMassNthPrimeLogHeight_pos N
    have hy : 0 < y := xiMassNthPrimeLogHeight_pos (N + 1)
    have hdelta0 : 0 ≤ delta := xiHeatCassiniOrderedPrimeLogGap_nonneg N
    have hdelta1 : delta ≤ 1 := xiHeatCassiniOrderedPrimeLogGap_le_one N
    have hy_eq : y = h + delta := by
      dsimp only [y, h, delta, xiHeatCassiniOrderedPrimeLogGap]
      ring
    have hy_le : y ≤ h + 1 := by linarith
    have hwold :=
      (woldCoeff_one_le_harmonic_le_eight_mul_woldCoeff_one
        (nthPrimeSubtype (N + 1))).1
    have hharmonic :
        xiMassPrimeHarmonicRealCoefficient (nthPrimeSubtype (N + 1)) =
          y * Real.exp (-y) := by
      unfold xiMassPrimeHarmonicRealCoefficient
      dsimp only [y, xiMassNthPrimeLogHeight]
      rw [Real.exp_neg,
        Real.exp_log (nthPrimeSubtype_pos (N + 1))]
      ring
    rw [hharmonic] at hwold
    have hexp : Real.exp (-y) ≤ Real.exp (-h) := by
      apply Real.exp_le_exp.mpr
      rw [hy_eq]
      linarith
    have hyexp : y * Real.exp (-y) ≤ (h + 1) * Real.exp (-h) := by
      calc
        y * Real.exp (-y) ≤ y * Real.exp (-h) :=
          mul_le_mul_of_nonneg_left hexp hy.le
        _ ≤ (h + 1) * Real.exp (-h) :=
          mul_le_mul_of_nonneg_right hy_le (Real.exp_nonneg _)
    have hwold' :
        woldCoeff 1 (nthPrimeSubtype (N + 1)) ≤
          (h + 1) * Real.exp (-h) := hwold.trans hyexp
    have hscale : 0 ≤ delta * Real.exp (h / 2) :=
      mul_nonneg hdelta0 (Real.exp_nonneg _)
    calc
      woldCoeff 1 (nthPrimeSubtype (N + 1)) *
            xiHeatCassiniOrderedPrimeLogGap N *
              Real.exp (xiMassNthPrimeLogHeight N / 2) =
          woldCoeff 1 (nthPrimeSubtype (N + 1)) *
            (delta * Real.exp (h / 2)) := by
              dsimp only [delta, h]
              ring
      _ ≤ ((h + 1) * Real.exp (-h)) *
            (delta * Real.exp (h / 2)) :=
          mul_le_mul_of_nonneg_right hwold' hscale
      _ = delta * h * Real.exp (-(1 / 2 : ℝ) * h) +
            delta * Real.exp (-(1 / 2 : ℝ) * h) := by
          have hexp : Real.exp (-h) * Real.exp (h / 2) =
              Real.exp (-(1 / 2 : ℝ) * h) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [show ((h + 1) * Real.exp (-h)) *
              (delta * Real.exp (h / 2)) =
                (h + 1) * delta *
                  (Real.exp (-h) * Real.exp (h / 2)) by ring,
            hexp]
          ring
      _ = xiHeatCassiniOrderedPrimeLogGap N *
              xiMassNthPrimeLogHeight N *
                Real.exp (-(1 / 2 : ℝ) * xiMassNthPrimeLogHeight N) +
            xiHeatCassiniOrderedPrimeLogGap N *
                Real.exp (-(1 / 2 : ℝ) * xiMassNthPrimeLogHeight N) := by
          rfl

/-- Two endpoint residual variations force the critical square of every logarithmic prime cell. -/
theorem summable_primeLogGap_sq_mul_criticalHalfDensity_of_twoSidedVariation
    (hleft : Summable
      (xiHeatCassiniWoldResidualUpperVariationAtom (1 / 2)))
    (hright : Summable
      (xiHeatCassiniWoldResidualRightUpperVariationAtom (1 / 2))) :
    Summable (fun N : ℕ =>
      xiHeatCassiniOrderedPrimeLogGap N ^ 2 *
        Real.exp (xiMassNthPrimeLogHeight N / 2)) := by
  have hmajor :=
    summable_woldCoeff_mul_primeLogGap_mul_criticalHalfDensity.add
      (hleft.add hright)
  refine Summable.of_nonneg_of_le (fun N => ?_) (fun N => ?_) hmajor
  · exact mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)
  · let h : ℝ := xiMassNthPrimeLogHeight N
    let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
    let R : ℝ := xiHeatCassiniOrderedWoldResidualLogDiscrepancy N
    let S : ℝ := xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1)
    let w : ℝ := woldCoeff 1 (nthPrimeSubtype (N + 1))
    have hdelta : 0 ≤ delta := xiHeatCassiniOrderedPrimeLogGap_nonneg N
    have hw : 0 ≤ w := woldCoeff_nonneg 1 _
    have hincrement :=
      xiHeatCassiniOrderedWoldResidualLogDiscrepancy_succ_sub N
    have hidentity : delta = w + R - S := by
      dsimp only [delta, w, R, S, xiHeatCassiniOrderedPrimeLogGap]
      linarith
    have hcell : delta ≤ w + |R| + |S| := by
      rw [hidentity]
      linarith [le_abs_self R, neg_le_abs S]
    have hscale : 0 ≤ delta * Real.exp (h / 2) :=
      mul_nonneg hdelta (Real.exp_nonneg _)
    calc
      xiHeatCassiniOrderedPrimeLogGap N ^ 2 *
            Real.exp (xiMassNthPrimeLogHeight N / 2) =
          delta * (delta * Real.exp (h / 2)) := by
            dsimp only [delta, h]
            ring
      _ ≤ (w + |R| + |S|) * (delta * Real.exp (h / 2)) :=
          mul_le_mul_of_nonneg_right hcell hscale
      _ = woldCoeff 1 (nthPrimeSubtype (N + 1)) *
              xiHeatCassiniOrderedPrimeLogGap N *
                Real.exp (xiMassNthPrimeLogHeight N / 2) +
            (xiHeatCassiniWoldResidualUpperVariationAtom (1 / 2) N +
              xiHeatCassiniWoldResidualRightUpperVariationAtom (1 / 2) N) := by
          dsimp only [w, R, S, delta, h,
            xiHeatCassiniWoldResidualUpperVariationAtom,
            xiHeatCassiniWoldResidualRightUpperVariationAtom]
          ring

/-- The two-sided residual graph norm forces critical additive prime-gap energy. -/
theorem summable_primeGapCriticalEnergy_of_half_twoSidedResidualUpperVariation
    (hleft : Summable
      (xiHeatCassiniWoldResidualUpperVariationAtom (1 / 2)))
    (hright : Summable
      (xiHeatCassiniWoldResidualRightUpperVariationAtom (1 / 2))) :
    Summable xiHeatCassiniPrimeGapCriticalEnergy := by
  have hlog :=
    summable_primeLogGap_sq_mul_criticalHalfDensity_of_twoSidedVariation
      hleft hright
  have hmajor := hlog.mul_left 4
  refine Summable.of_nonneg_of_le
    xiHeatCassiniPrimeGapCriticalEnergy_nonneg (fun N => ?_) hmajor
  let p : ℝ := nthPrimeSubtype N
  let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  have hp : 0 < p := nthPrimeSubtype_pos N
  have hdelta : 0 ≤ delta := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hgap : 0 ≤ xiHeatCassiniOrderedPrimeGap N :=
    xiHeatCassiniOrderedPrimeGap_nonneg N
  have hnormalized0 : 0 ≤ xiHeatCassiniOrderedPrimeGap N / p :=
    div_nonneg hgap hp.le
  have hnormalized :
      xiHeatCassiniOrderedPrimeGap N / p ≤ 2 * delta := by
    have hbase := primeGap_div_two_prime_le_primeLogGap N
    dsimp only [p, delta] at hbase ⊢
    calc
      xiHeatCassiniOrderedPrimeGap N / (nthPrimeSubtype N : ℝ) =
          2 * (xiHeatCassiniOrderedPrimeGap N /
            (2 * (nthPrimeSubtype N : ℝ))) := by
        field_simp [hp.ne']
      _ ≤ 2 * xiHeatCassiniOrderedPrimeLogGap N :=
        mul_le_mul_of_nonneg_left hbase (by norm_num)
  have hsqrt : Real.sqrt p =
      Real.exp (xiMassNthPrimeLogHeight N / 2) := by
    rw [xiMassNthPrimeLogHeight]
    rw [← Real.exp_log (Real.sqrt_pos.mpr hp)]
    congr 1
    exact Real.log_sqrt hp.le
  unfold xiHeatCassiniPrimeGapCriticalEnergy
  change (xiHeatCassiniOrderedPrimeGap N / p) ^ 2 * Real.sqrt p ≤ _
  rw [hsqrt]
  calc
    (xiHeatCassiniOrderedPrimeGap N / p) ^ 2 *
          Real.exp (xiMassNthPrimeLogHeight N / 2) ≤
        (2 * delta) ^ 2 *
          Real.exp (xiMassNthPrimeLogHeight N / 2) := by
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ hnormalized0 (mul_nonneg (by norm_num) hdelta)).2
          hnormalized)
        (Real.exp_nonneg _)
    _ = 4 * (xiHeatCassiniOrderedPrimeLogGap N ^ 2 *
          Real.exp (xiMassNthPrimeLogHeight N / 2)) := by
      dsimp only [delta]
      ring

/-- **Single-norm Route-T closure.**  Summability of the two endpoint halves of the critical Abel
graph norm forces RH.  No independent prime-gap hypothesis remains. -/
theorem riemannHypothesis_of_half_twoSided_residualUpperVariation
    (hleft : Summable
      (xiHeatCassiniWoldResidualUpperVariationAtom (1 / 2)))
    (hright : Summable
      (xiHeatCassiniWoldResidualRightUpperVariationAtom (1 / 2))) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_half_residualUpperVariation_criticalEnergy
    hleft
    (summable_primeGapCriticalEnergy_of_half_twoSidedResidualUpperVariation
      hleft hright)

end

end RHTower
