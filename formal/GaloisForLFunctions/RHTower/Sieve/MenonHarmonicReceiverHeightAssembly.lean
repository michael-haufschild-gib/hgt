import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicReceiverHeightProduct
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRoughSchedule
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicFullLadderError

namespace RHTower.Sieve

open Filter Finset MeasureTheory

noncomputable section

/-- Explicit scalar multiplying the square of one prime-block threshold at receiver height `W`. -/
def menonFinalReceiverCostEnvelope (x W volE : ℝ) (j : ℕ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    (24 * (6 +
      80000 * Real.sqrt W * Real.log x * (2 * Real.pi * volE) *
        (menonFinalRangeLadderBase x *
          (1 + menonFinalRangeLadderEta x) ^ j) / x +
      144 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * W))))

private theorem setIntegral_normSq_menonFinalRangeShell_le_receiver_thresholds_exactDefect
    {x Q eta W : ℝ} {L : ℕ} (hQ : 1 < Q) (heta : 0 ≤ eta)
    (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPrange : ∀ p ∈ menonFinalRangePrimes x,
      Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (V M : ℕ → ℝ)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(⌈x⌉₊ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(menonFinalRangeTopNat x : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hlargeVolume : ∀ j ∈ Finset.range L,
      volume.real (menonHarmonicPrimeBlockLargeOn E
        (geomBlock (menonFinalRangePrimes x) Q (1 + eta) j) (V j)) ≤ M j) :
    (∫ w in E,
      ‖logPoly harmonicMoebiusC (menonFinalRangeShell x) w‖ ^ 2) ≤
      2 * (2 * (L : ℝ) * ∑ j ∈ Finset.range L,
        (menonHarmonicProductCostVolume (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta W (V j) (volume.real E) j +
          menonHarmonicProductCostVolume (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta W
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
      (B₀ := menonFinalRangeTopNat x) (L := L) (Q := Q) (eta := eta) (W := W)
      hQ heta hW hL (fun p hp => menonFinalRangePrimes_prime x hp)
      hPrange V M hleft hright hEm hEs hlargeVolume
  have hsplit := setIntegral_normSq_add_le
    (F := fun w => harmonicRamareBilinear (menonFinalRangePrimes x)
      (menonFinalRangeShell x) w)
    (G := fun w => logPoly harmonicMoebiusC (menonFinalRangeHarmonicRoughSet x) w)
    (E := E) (W := W)
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

/-- Closed final-schedule shell assembly at the actual receiver height.  Every strict block-large
set enters with its exact measure; no exceptional-set estimate is assumed. -/
theorem eventually_setIntegral_normSq_menonFinalRangeShell_le_receiver_actualLargeVolumes :
    ∀ᶠ x : ℝ in atTop, ∀ W : ℝ, 1 ≤ W → W ≤ x →
      ∀ (V : ℕ → ℝ) {E : Set ℝ}, MeasurableSet E → E ⊆ Set.Icc (-W) W →
      (∫ w in E,
        ‖logPoly harmonicMoebiusC (menonFinalRangeShell x) w‖ ^ 2) ≤
        4 * (menonFinalRangeLadderSteps x : ℝ) *
          ∑ j ∈ Finset.range (menonFinalRangeLadderSteps x),
            (menonHarmonicProductCostVolume (menonFinalRangePrimes x) ⌈x⌉₊
                (menonFinalRangeTopNat x) (menonFinalRangeLadderBase x)
                (menonFinalRangeLadderEta x) W (V j) (volume.real E) j +
              menonHarmonicProductCostVolume (menonFinalRangePrimes x) ⌈x⌉₊
                (menonFinalRangeTopNat x) (menonFinalRangeLadderBase x)
                (menonFinalRangeLadderEta x) W
                (harmonicPrimeMass (geomBlock (menonFinalRangePrimes x)
                  (menonFinalRangeLadderBase x)
                  (1 + menonFinalRangeLadderEta x) j))
                (volume.real (menonHarmonicPrimeBlockLargeOn E
                  (geomBlock (menonFinalRangePrimes x) (menonFinalRangeLadderBase x)
                    (1 + menonFinalRangeLadderEta x) j) (V j))) j) +
          18 * (Real.log x) ^ (-(8 : ℝ)) := by
  filter_upwards [eventually_menonFinalRangeLadder_basic,
    eventually_menonFinalRangePrimes_ladder_range,
    eventually_menonFinalRangeLadder_cofactor_endpoints,
    eventually_integral_menonFinalRange_fullLadderDefect_le_four_log_rpow_neg_eight,
    eventually_menonFinalRangeHarmonicRoughEnergy_le_log_rpow_neg_eight] with
      x hbasic hPrange hendpoints hdefect hrough
  intro W hW hWx V E hEm hEs
  rcases hbasic with ⟨hx, _, hQ, _, heta, hL⟩
  let M : ℕ → ℝ := fun j =>
    volume.real (menonHarmonicPrimeBlockLargeOn E
      (geomBlock (menonFinalRangePrimes x) (menonFinalRangeLadderBase x)
        (1 + menonFinalRangeLadderEta x) j) (V j))
  have hbase := setIntegral_normSq_menonFinalRangeShell_le_receiver_thresholds_exactDefect
    (x := x) (Q := menonFinalRangeLadderBase x) (eta := menonFinalRangeLadderEta x)
    (W := W) (L := menonFinalRangeLadderSteps x) hQ heta hW hL hPrange V M
    (fun j hj => (hendpoints j hj).1) (fun j hj => (hendpoints j hj).2)
    hEm hEs (fun _ _ => le_rfl)
  have hdefectE :
      (∫ w in E,
        ‖harmonicLadderProductDefect (menonFinalRangePrimes x) ⌈x⌉₊
          (menonFinalRangeTopNat x) (menonFinalRangeLadderBase x)
          (menonFinalRangeLadderEta x) (menonFinalRangeLadderSteps x) w‖ ^ 2) ≤
        4 * (Real.log x) ^ (-(8 : ℝ)) := by
    calc
      _ ≤ ∫ w in Set.Icc (-W) W,
          ‖harmonicLadderProductDefect (menonFinalRangePrimes x) ⌈x⌉₊
            (menonFinalRangeTopNat x) (menonFinalRangeLadderBase x)
            (menonFinalRangeLadderEta x) (menonFinalRangeLadderSteps x) w‖ ^ 2 := by
        have hf := (continuous_harmonicLadderProductDefect
          (menonFinalRangePrimes x) ⌈x⌉₊ (menonFinalRangeTopNat x)
          (menonFinalRangeLadderBase x) (menonFinalRangeLadderEta x)
          (menonFinalRangeLadderSteps x)).norm.pow 2
        exact MeasureTheory.setIntegral_mono_set hf.integrableOn_Icc
          (Filter.Eventually.of_forall fun _ => by positivity)
          (Filter.Eventually.of_forall hEs)
      _ ≤ _ := hdefect W hW hWx
  have hroughE :
      (∫ w in E,
        ‖logPoly harmonicMoebiusC (menonFinalRangeHarmonicRoughSet x) w‖ ^ 2) ≤
        (Real.log x) ^ (-(8 : ℝ)) := by
    have hsub : E ⊆ Set.Icc (-x) x := by
      intro w hw
      have hw' := hEs hw
      exact ⟨by linarith [hw'.1], by linarith [hw'.2]⟩
    calc
      _ ≤ menonFinalRangeHarmonicRoughEnergy x := by
        rw [menonFinalRangeHarmonicRoughEnergy]
        have hf := (continuous_logPoly harmonicMoebiusC
          (menonFinalRangeHarmonicRoughSet x)).norm.pow 2
        exact MeasureTheory.setIntegral_mono_set hf.integrableOn_Icc
          (Filter.Eventually.of_forall fun _ => by positivity)
          (Filter.Eventually.of_forall hsub)
      _ ≤ _ := hrough
  dsimp only [M] at hbase
  calc
    _ ≤ 2 * (2 * (menonFinalRangeLadderSteps x : ℝ) *
          ∑ j ∈ Finset.range (menonFinalRangeLadderSteps x),
            (menonHarmonicProductCostVolume (menonFinalRangePrimes x) ⌈x⌉₊
                (menonFinalRangeTopNat x) (menonFinalRangeLadderBase x)
                (menonFinalRangeLadderEta x) W (V j) (volume.real E) j +
              menonHarmonicProductCostVolume (menonFinalRangePrimes x) ⌈x⌉₊
                (menonFinalRangeTopNat x) (menonFinalRangeLadderBase x)
                (menonFinalRangeLadderEta x) W
                (harmonicPrimeMass (geomBlock (menonFinalRangePrimes x)
                  (menonFinalRangeLadderBase x)
                  (1 + menonFinalRangeLadderEta x) j))
                (volume.real (menonHarmonicPrimeBlockLargeOn E
                  (geomBlock (menonFinalRangePrimes x) (menonFinalRangeLadderBase x)
                    (1 + menonFinalRangeLadderEta x) j) (V j))) j) +
          2 * (4 * (Real.log x) ^ (-(8 : ℝ)))) +
        2 * (Real.log x) ^ (-(8 : ℝ)) := by
          refine hbase.trans ?_
          gcongr
    _ = _ := by ring

/-- Closed receiver-height assembly with both product costs expanded.  The only block-local data
left are the chosen thresholds and the exact measures of their strict large-value sets. -/
theorem eventually_setIntegral_normSq_menonFinalRangeShell_le_receiver_explicitLargeVolumes :
    ∀ᶠ x : ℝ in atTop, ∀ W : ℝ, 1 ≤ W → W ≤ x →
      ∀ (V : ℕ → ℝ) {E : Set ℝ}, MeasurableSet E → E ⊆ Set.Icc (-W) W →
      (∫ w in E,
        ‖logPoly harmonicMoebiusC (menonFinalRangeShell x) w‖ ^ 2) ≤
        4 * (menonFinalRangeLadderSteps x : ℝ) *
          ∑ j ∈ Finset.range (menonFinalRangeLadderSteps x),
            ((V j) ^ 2 * menonFinalReceiverCostEnvelope x W (volume.real E) j +
              (harmonicPrimeMass (geomBlock (menonFinalRangePrimes x)
                (menonFinalRangeLadderBase x)
                (1 + menonFinalRangeLadderEta x) j)) ^ 2 *
                menonFinalReceiverCostEnvelope x W
                  (volume.real (menonHarmonicPrimeBlockLargeOn E
                    (geomBlock (menonFinalRangePrimes x) (menonFinalRangeLadderBase x)
                      (1 + menonFinalRangeLadderEta x) j) (V j))) j) +
          18 * (Real.log x) ^ (-(8 : ℝ)) := by
  filter_upwards [
    eventually_setIntegral_normSq_menonFinalRangeShell_le_receiver_actualLargeVolumes,
    eventually_menonFinalReceiverProductCostVolume_le_explicit] with x hassembly hcost
  intro W hW hWx V E hEm hEs
  have hbase := hassembly W hW hWx V hEm hEs
  refine hbase.trans ?_
  gcongr with j hj
  · simpa only [menonFinalReceiverCostEnvelope] using
      hcost W hW hWx (menonFinalRangePrimes x) (V j) (volume.real E) j hj
        measureReal_nonneg
  · simpa only [menonFinalReceiverCostEnvelope] using
      hcost W hW hWx (menonFinalRangePrimes x)
        (harmonicPrimeMass (geomBlock (menonFinalRangePrimes x)
          (menonFinalRangeLadderBase x) (1 + menonFinalRangeLadderEta x) j))
        (volume.real (menonHarmonicPrimeBlockLargeOn E
          (geomBlock (menonFinalRangePrimes x) (menonFinalRangeLadderBase x)
            (1 + menonFinalRangeLadderEta x) j) (V j))) j hj
        measureReal_nonneg

end

end RHTower.Sieve
