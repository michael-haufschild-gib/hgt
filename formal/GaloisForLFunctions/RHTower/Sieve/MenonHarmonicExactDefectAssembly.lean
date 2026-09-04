import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicExternalFrequencyAssembly
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicNarrowBlockComparison

/-!
# Harmonic frequency assembly with the exact global defect

The earlier external-frequency assembly closes the moving-support defect by its coarse universal
budget.  This file keeps the literal defect integral through the same threshold partition, so a
sharper schedule-specific defect theorem can be inserted without changing any block estimate.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Complete harmonic ladder on an external frequency set, with the literal global support defect
retained and every strict block-large measure exposed separately. -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_external_thresholds_exactDefect
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W : ℝ}
    (hQ : 1 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (V M : ℕ → ℝ)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hlargeVolume : ∀ j ∈ Finset.range L,
      volume.real (menonHarmonicPrimeBlockLargeOn E
        (geomBlock P Q (1 + eta) j) (V j)) ≤ M j) :
    (∫ w in E, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2) ≤
      2 * (L : ℝ) * ∑ j ∈ Finset.range L,
        (menonHarmonicProductCostVolume P A₀ B₀ Q eta W
            (V j) (volume.real E) j +
          menonHarmonicProductCostVolume P A₀ B₀ Q eta W
            (harmonicPrimeMass (geomBlock P Q (1 + eta) j)) (M j) j) +
        2 * ∫ w in E,
          ‖harmonicLadderProductDefect P A₀ B₀ Q eta L w‖ ^ 2 := by
  have hbase := setIntegral_normSq_harmonicRamareBilinear_le_ladder_error
    (P := P) A₀ B₀ (lt_trans zero_lt_one hQ) heta hL hPprime hPrange hEm hEs
  refine hbase.trans (add_le_add ?_ le_rfl)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_)
    (mul_nonneg (by norm_num) (Nat.cast_nonneg L))
  exact setIntegral_normSq_harmonicProduct_geom_le_threshold_largeMeasure
    hW j hPprime (hleft j hj) (hright j hj) hEm hEs (hlargeVolume j hj)

/-- Menon's literal final-range shell on an external frequency set, with the exact global defect
and exact rough remainder both retained. -/
theorem setIntegral_normSq_menonFinalRangeShell_le_external_thresholds_exactDefect
    {x Q eta : ℝ} {L : ℕ} (hx : 1 ≤ x) (hQ : 1 < Q) (heta : 0 ≤ eta) (hL : 1 ≤ L)
    (hPrange : ∀ p ∈ menonFinalRangePrimes x,
      Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (V M : ℕ → ℝ)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(⌈x⌉₊ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(menonFinalRangeTopNat x : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-x) x)
    (hlargeVolume : ∀ j ∈ Finset.range L,
      volume.real (menonHarmonicPrimeBlockLargeOn E
        (geomBlock (menonFinalRangePrimes x) Q (1 + eta) j) (V j)) ≤ M j) :
    (∫ w in E,
      ‖logPoly harmonicMoebiusC (menonFinalRangeShell x) w‖ ^ 2) ≤
      2 * (2 * (L : ℝ) * ∑ j ∈ Finset.range L,
        (menonHarmonicProductCostVolume (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta x (V j) (volume.real E) j +
          menonHarmonicProductCostVolume (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta x
            (harmonicPrimeMass
              (geomBlock (menonFinalRangePrimes x) Q (1 + eta) j)) (M j) j) +
        2 * ∫ w in E,
          ‖harmonicLadderProductDefect (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta L w‖ ^ 2) +
      2 * ∫ w in E,
        ‖logPoly harmonicMoebiusC (menonFinalRangeHarmonicRoughSet x) w‖ ^ 2 := by
  have hbil :=
    setIntegral_normSq_harmonicRamareBilinear_le_external_thresholds_exactDefect
      (P := menonFinalRangePrimes x) (A₀ := ⌈x⌉₊)
      (B₀ := menonFinalRangeTopNat x) (L := L) (Q := Q) (eta := eta) (W := x)
      hQ heta hx hL (fun p hp => menonFinalRangePrimes_prime x hp)
      hPrange V M hleft hright hEm hEs hlargeVolume
  have hsplit := setIntegral_normSq_add_le
    (F := fun w => harmonicRamareBilinear (menonFinalRangePrimes x)
      (menonFinalRangeShell x) w)
    (G := fun w => logPoly harmonicMoebiusC (menonFinalRangeHarmonicRoughSet x) w)
    (E := E) (W := x)
    (by
      refine continuous_finsetSum (menonFinalRangePrimes x) fun p _ => ?_
      exact ((continuous_moebiusPhase p).div_const _).mul (continuous_logPoly _ _))
    (continuous_logPoly _ _) hEm hEs
  calc
    (∫ w in E,
      ‖logPoly harmonicMoebiusC (menonFinalRangeShell x) w‖ ^ 2) ≤
        2 * (∫ w in E,
          ‖harmonicRamareBilinear (menonFinalRangePrimes x)
            (menonFinalRangeShell x) w‖ ^ 2) +
        2 * ∫ w in E,
          ‖logPoly harmonicMoebiusC (menonFinalRangeHarmonicRoughSet x) w‖ ^ 2 := by
            simpa only [logPoly_harmonicMoebius_eq_menonFinalRange_ramare_add_rough,
              menonFinalRangeHarmonicRoughSet] using hsplit
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hbil (by norm_num)) le_rfl

/-- Ordinary all-small initial-range frequencies control the complete harmonic Ramaré ladder,
while retaining the literal global support defect. -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_ordinary_allSmall_exactDefect
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta theta W : ℝ}
    (hQ : 1 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊) :
    let E := allBlocksSmall P Q eta L
      (fun j => ((geomBlock P Q (1 + eta) j).card : ℝ) * theta) W
    (∫ w in E,
      ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2) ≤
      2 * (L : ℝ) * ∑ j ∈ Finset.range L,
        menonHarmonicProductCostVolume P A₀ B₀ Q eta W
          (((geomBlock P Q (1 + eta) j).card : ℝ) * (theta + eta) /
            (Q * (1 + eta) ^ j)) (volume.real E) j +
        2 * ∫ w in E,
          ‖harmonicLadderProductDefect P A₀ B₀ Q eta L w‖ ^ 2 := by
  classical
  let E := allBlocksSmall P Q eta L
    (fun j => ((geomBlock P Q (1 + eta) j).card : ℝ) * theta) W
  have hEm : MeasurableSet E := by
    simpa only [E] using measurableSet_allBlocksSmall P Q eta L
      (fun j => ((geomBlock P Q (1 + eta) j).card : ℝ) * theta) W
  have hEs : E ⊆ Set.Icc (-W) W := by
    simpa only [E] using allBlocksSmall_subset P Q eta L
      (fun j => ((geomBlock P Q (1 + eta) j).card : ℝ) * theta) W
  have hbase := setIntegral_normSq_harmonicRamareBilinear_le_ladder_error
    (P := P) A₀ B₀ (lt_trans zero_lt_one hQ) heta hL hPprime hPrange hEm hEs
  refine hbase.trans (add_le_add ?_ le_rfl)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_)
    (mul_nonneg (by norm_num) (Nat.cast_nonneg L))
  exact setIntegral_normSq_harmonicProduct_geom_le_HM
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (W := W)
    (V := ((geomBlock P Q (1 + eta) j).card : ℝ) * (theta + eta) /
      (Q * (1 + eta) ^ j)) hW j (hleft j hj) (hright j hj) hEm hEs
      (fun w hw =>
        norm_harmonicPrimeBlockPoly_le_of_mem_ordinary_allBlocksSmall
          (lt_trans zero_lt_one hQ) heta hj (by simpa only [E] using hw))

end

end RHTower.Sieve
