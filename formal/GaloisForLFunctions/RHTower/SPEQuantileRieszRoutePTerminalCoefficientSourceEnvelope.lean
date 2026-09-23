import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePTerminalCoefficientThreshold
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarParabolicOrientationLedger
import GaloisForLFunctions.RHTower.CCMActualHeadSignedCompletedErrorGammaProducer

open scoped BigOperators
open Filter

/-!
# Literal source envelope for Route-P's terminal coefficient

The quantile first moment telescopes to its endpoint square. This yields an
exact mass--centroid formula for the canonical shift and an unconditional
rectangular regime: fixed terminal scale, growing source head.

It does not identify a terminal scale with a source head or construct the
missing ordered-history terminal intertwiner.
-/

noncomputable section

namespace RHTower

private theorem quantile_coordinate_two :
    ccmActualHeadQuantilePolarCoordinate 2 = 2 := by
  rw [ccmActualHeadQuantilePolarCoordinate_eq_two_add_cumulative]
  have hzero : criticalMellinAtomWeight 0 = 0 := by
    simp [criticalMellinAtomWeight]
  have hone : criticalMellinAtomWeight 1 = 0 := by
    simp [criticalMellinAtomWeight]
  simp [ccmOutgoingPrimeCumulative, Finset.sum_range_succ, hzero, hone]

private theorem quantile_coordinate_terminal_eq_two_add_mass (K : ℕ) :
    ccmActualHeadQuantilePolarCoordinate (K + 3) =
      2 + ccmActualHeadParabolicMass K := by
  rw [ccmActualHeadQuantilePolarCoordinate_eq_two_add_cumulative]
  have hzero : criticalMellinAtomWeight 0 = 0 := by
    simp [criticalMellinAtomWeight]
  have hone : criticalMellinAtomWeight 1 = 0 := by
    simp [criticalMellinAtomWeight]
  unfold ccmOutgoingPrimeCumulative ccmActualHeadParabolicMass
  congr 1
  induction K with
  | zero => simp [Finset.sum_range_succ, hzero, hone]
  | succ K ih =>
      simpa [Finset.sum_range_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        congrArg (fun x : ℝ => x + criticalMellinAtomWeight (K + 3)) ih

private theorem sum_range_shift_two (F : ℕ → ℝ)
    (hzero : F 0 = 0) (hone : F 1 = 0) (K : ℕ) :
    (∑ n ∈ Finset.range (K + 3), F n) =
      ∑ n ∈ Finset.range (K + 1), F (n + 2) := by
  induction K with
  | zero => simp [Finset.sum_range_succ, hzero, hone]
  | succ K ih =>
      simpa [Finset.sum_range_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        congrArg (fun x : ℝ => x + F (K + 3)) ih

theorem ccmActualHeadQuantileParabolicAggregate_one_eq_mass_sq_div_two_add_two_mul_mass (K : ℕ) :
    ccmActualHeadQuantileParabolicAggregate K 1 =
      ccmActualHeadParabolicMass K ^ (2 : ℕ) / 2 + 2 * ccmActualHeadParabolicMass K := by
  unfold ccmActualHeadQuantileParabolicAggregate
  simp only [Finset.sum_apply]
  have hterms : ∀ n ∈ Finset.range (K + 1),
      ccmActualHeadQuantileParabolicMoment (n + 2) 1 =
        (ccmActualHeadQuantilePolarCoordinate (n + 3) ^ (2 : ℕ) -
          ccmActualHeadQuantilePolarCoordinate (n + 2) ^ (2 : ℕ)) / 2 := by
    intro n hn
    rfl
  calc
    _ = ∑ n ∈ Finset.range (K + 1),
        (ccmActualHeadQuantilePolarCoordinate (n + 3) ^ (2 : ℕ) -
          ccmActualHeadQuantilePolarCoordinate (n + 2) ^ (2 : ℕ)) / 2 := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hterms n hn
    _ = (∑ n ∈ Finset.range (K + 1),
        (ccmActualHeadQuantilePolarCoordinate (n + 3) ^ (2 : ℕ) -
          ccmActualHeadQuantilePolarCoordinate (n + 2) ^ (2 : ℕ))) / 2 := by
        rw [Finset.sum_div]
    _ = _ := by
      have htel := Finset.sum_range_sub
        (fun n : ℕ => ccmActualHeadQuantilePolarCoordinate (n + 2) ^ (2 : ℕ)) (K + 1)
      rw [quantile_coordinate_terminal_eq_two_add_mass, quantile_coordinate_two] at htel
      rw [htel]
      ring

private theorem matched_aggregate_one_eq_weighted_centroid_sum (K : ℕ) :
    ccmActualHeadMatchedParabolicAggregate K 1 =
      ∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) * ccmActualHeadMatchedPolarCentroid (n + 2) := by
  unfold ccmActualHeadMatchedParabolicAggregate
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  exact ccmActualHeadMatchedParabolicMoment_one_eq_weight_mul_centroid (n + 2)

theorem ccmActualHeadMatchedQuantileParabolicSourceBoundary_one_eq_mass_centroid_decomposition (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicSourceBoundary K 1 =
      (∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) * ccmActualHeadMatchedPolarCentroid (n + 2)) +
      ccmActualHeadParabolicMass K ^ (2 : ℕ) / 2 + 2 * ccmActualHeadParabolicMass K := by
  rw [ccmActualHeadMatchedQuantileParabolicSourceBoundary]
  simp only [Pi.add_apply]
  rw [matched_aggregate_one_eq_weighted_centroid_sum,
    ccmActualHeadQuantileParabolicAggregate_one_eq_mass_sq_div_two_add_two_mul_mass]
  ring

theorem ccmActualHeadMatchedQuantileParabolicCenteredShift_eq_mass_centroid_decomposition (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCenteredShift K =
      -1 - ccmActualHeadParabolicMass K / 4 -
        (∑ n ∈ Finset.range (K + 1),
          criticalMellinAtomWeight (n + 2) * ccmActualHeadMatchedPolarCentroid (n + 2)) /
          (2 * ccmActualHeadParabolicMass K) := by
  have hM : ccmActualHeadParabolicMass K ≠ 0 :=
    (ccmActualHeadParabolicMass_pos K).ne'
  unfold ccmActualHeadMatchedQuantileParabolicCenteredShift
  rw [ccmActualHeadMatchedQuantileParabolicSourceBoundary_one_eq_mass_centroid_decomposition,
    ccmActualHeadMatchedQuantileParabolicSourceBoundary_zero]
  field_simp [hM]
  ring

theorem ccmActualHeadMatchedQuantileParabolicCenteredShift_le_neg_one_sub_mass_quarter (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCenteredShift K ≤
      -1 - ccmActualHeadParabolicMass K / 4 := by
  rw [ccmActualHeadMatchedQuantileParabolicCenteredShift_eq_mass_centroid_decomposition]
  have hsum : 0 ≤ ∑ n ∈ Finset.range (K + 1),
      criticalMellinAtomWeight (n + 2) * ccmActualHeadMatchedPolarCentroid (n + 2) := by
    apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _)
      (ccmActualHeadMatchedPolarCentroid_pos _).le
  have hmass : 0 < ccmActualHeadParabolicMass K := ccmActualHeadParabolicMass_pos K
  have hdiv : 0 ≤
      (∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) * ccmActualHeadMatchedPolarCentroid (n + 2)) /
        (2 * ccmActualHeadParabolicMass K) := by positivity
  linarith

theorem speQuantileRiesz_terminalCoefficient_nonpos_of_le_mass_envelope (M K : ℕ)
    (hM : (M : ℝ) ≤ (1 + ccmActualHeadParabolicMass K / 4) ^ (2 : ℕ)) :
    Real.sqrt (M : ℝ) + ccmActualHeadMatchedQuantileParabolicCenteredShift K ≤ 0 := by
  apply speQuantileRiesz_terminalCoefficient_nonpos_iff M K |>.mpr
  have hshift := ccmActualHeadMatchedQuantileParabolicCenteredShift_le_neg_one_sub_mass_quarter K
  have hmass : 0 < ccmActualHeadParabolicMass K := ccmActualHeadParabolicMass_pos K
  have hscale : 0 ≤ 1 + ccmActualHeadParabolicMass K / 4 := by positivity
  have hprod : 0 ≤
      (ccmActualHeadMatchedQuantileParabolicCenteredShift K +
        (1 + ccmActualHeadParabolicMass K / 4)) *
      (ccmActualHeadMatchedQuantileParabolicCenteredShift K -
        (1 + ccmActualHeadParabolicMass K / 4)) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  nlinarith

theorem ccmActualHeadParabolicMass_tendsto_atTop :
    Tendsto ccmActualHeadParabolicMass atTop atTop := by
  have hzero : criticalMellinAtomWeight 0 ^ (2 : ℕ) = 0 := by
    simp [criticalMellinAtomWeight]
  have hone : criticalMellinAtomWeight 1 ^ (2 : ℕ) = 0 := by
    simp [criticalMellinAtomWeight]
  have hsq : Tendsto (fun K : ℕ =>
      ∑ n ∈ Finset.range (K + 1), criticalMellinAtomWeight (n + 2) ^ (2 : ℕ)) atTop atTop := by
    have h := tendsto_criticalMellinAtomWeight_squarePartialSum_atTop.comp
      (tendsto_add_atTop_nat 3)
    refine h.congr' (Eventually.of_forall fun K => ?_)
    exact sum_range_shift_two (fun n => criticalMellinAtomWeight n ^ (2 : ℕ)) hzero hone K
  have hscaled := Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) hsq
  refine tendsto_atTop_mono' atTop ?_ hscaled
  filter_upwards with K
  unfold ccmActualHeadParabolicMass
  have hterm : ∀ n ∈ Finset.range (K + 1),
      criticalMellinAtomWeight (n + 2) ^ (2 : ℕ) ≤
        2 * criticalMellinAtomWeight (n + 2) := by
    intro n hn
    have hnonneg : 0 ≤ criticalMellinAtomWeight (n + 2) :=
      criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _
    have hupper : criticalMellinAtomWeight (n + 2) ≤ 2 :=
      criticalMellinAtomWeight_le_two_of_pos (by omega)
    nlinarith
  have hsum := Finset.sum_le_sum hterm
  calc
    (1 / 2 : ℝ) * ∑ n ∈ Finset.range (K + 1), criticalMellinAtomWeight (n + 2) ^ (2 : ℕ) ≤
        (1 / 2 : ℝ) * ∑ n ∈ Finset.range (K + 1),
          2 * criticalMellinAtomWeight (n + 2) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = ∑ n ∈ Finset.range (K + 1), criticalMellinAtomWeight (n + 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring

theorem speQuantileRiesz_terminalCoefficient_eventually_nonpos_in_head (M : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      Real.sqrt (M : ℝ) + ccmActualHeadMatchedQuantileParabolicCenteredShift K ≤ 0 := by
  have hmass := ccmActualHeadParabolicMass_tendsto_atTop
  filter_upwards [hmass.eventually_ge_atTop (4 * Real.sqrt (M : ℝ))] with K hK
  apply speQuantileRiesz_terminalCoefficient_nonpos_of_le_mass_envelope M K
  have hroot : Real.sqrt (M : ℝ) ^ (2 : ℕ) = M :=
    Real.sq_sqrt (Nat.cast_nonneg M)
  have hroot_nonneg : 0 ≤ Real.sqrt (M : ℝ) := Real.sqrt_nonneg _
  nlinarith

end RHTower
