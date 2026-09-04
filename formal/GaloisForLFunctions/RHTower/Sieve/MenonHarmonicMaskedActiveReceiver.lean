import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicMaskedReceiver
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicMaskedActiveSupport

/-!
# Support-aware receiver for the masked second Ramaré range

The initial non-rough mask forces every relevant final prime `p` to satisfy `p Q₀ < B₀`, where
`Q₀` is the lower endpoint of the initial prime range and `B₀` is the final shell top.  Running the
second Ramaré decomposition only over those active primes removes every formally empty high block
before the product costs are estimated.
-/

namespace RHTower.Sieve

open Filter Finset MeasureTheory Topology

noncomputable section

/-- Menon's closed full-ladder defect budget is monotone at the source level: every subset of the
literal final prime range satisfies the same estimate. -/
theorem eventually_integral_menonFinalRange_subsetLadderDefectWithCoeff_le_four_log_rpow_neg_eight :
    ∀ᶠ x : ℝ in atTop, ∀ (P : Finset ℕ), P ⊆ menonFinalRangePrimes x →
      ∀ (c : ℕ → ℂ), (∀ {m : ℕ}, 0 < m → ‖c m‖ ≤ 1 / (m : ℝ)) →
      ∀ W : ℝ, 1 ≤ W → W ≤ x →
      (∫ w in Set.Icc (-W) W,
        ‖harmonicLadderProductDefectWithCoeff P ⌈x⌉₊
          (menonFinalRangeTopNat x) (menonFinalRangeLadderBase x)
          (menonFinalRangeLadderEta x) (menonFinalRangeLadderSteps x) c w‖ ^ 2) ≤
        4 * (Real.log x) ^ (-(8 : ℝ)) := by
  filter_upwards [eventually_menonTruncatedRangeLadder_basic,
    eventually_menonFinalRangeLadder_basic,
    eventually_menonTruncatedRangeLadderSteps_le_finalRangeLadderSteps,
    eventually_menonTruncatedRangeLadder_cover,
    eventually_menonFinalRangeTopNat_lt_truncatedPrimeTopNat_sq,
    eventually_menonTruncatedRange_ladderErrorBudget_le_log_rpow_neg_eight,
    eventually_menonFinalRange_highLadderErrorBudget_le_log_rpow_neg_eight] with
      x htrunc _hfull hJL hcover hsep hlo hhi
  intro P hPsub c hc W hW hWx
  rcases htrunc with ⟨hxone, _, _, hQ, _, heta, _⟩
  rcases hsep with ⟨hU, hU2⟩
  have hA : 0 < ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr (lt_trans zero_lt_one hxone)
  have hPprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact menonFinalRangePrimes_prime x (hPsub hp)
  have hPge : ∀ p ∈ P, menonFinalRangeLadderBase x ≤ (p : ℝ) := by
    intro p hp
    have hpRange := mem_primesRange.mp (hPsub hp)
    rw [menonFinalRangeLadderBase]
    exact_mod_cast hpRange.2.1.le
  have hbase := integral_Icc_normSq_harmonicLadderProductDefectWithCoeff_le_prefix_add_high
    hc (P := P) (A₀ := ⌈x⌉₊) (B₀ := menonFinalRangeTopNat x)
    (Q := menonFinalRangeLadderBase x) (eta := menonFinalRangeLadderEta x)
    (U := (menonTruncatedPrimeTopNat x : ℝ)) (W := W)
    (J := menonTruncatedRangeLadderSteps x) (L := menonFinalRangeLadderSteps x)
    hA hQ heta hW hJL hPprime hPge hcover (by exact_mod_cast hU) hU2
  calc
    _ ≤ 2 * menonHarmonicLadderErrorBudget ⌈x⌉₊ (menonFinalRangeTopNat x)
          (menonFinalRangeLadderBase x) (menonFinalRangeLadderEta x) W
          (menonTruncatedRangeLadderSteps x) +
        2 * menonHarmonicHighLadderErrorBudget ⌈x⌉₊ (menonFinalRangeTopNat x)
          (menonFinalRangeLadderEta x) (menonTruncatedPrimeTopNat x : ℝ) W := hbase
    _ ≤ 2 * (Real.log x) ^ (-(8 : ℝ)) + 2 * (Real.log x) ^ (-(8 : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left (hlo W (by linarith) hWx) (by norm_num))
        (mul_le_mul_of_nonneg_left (hhi W (by linarith) hWx) (by norm_num))
    _ = 4 * (Real.log x) ^ (-(8 : ℝ)) := by ring

/-- Receiver-height assembly over exactly the final primes compatible with the initial mask. -/
theorem eventually_setIntegral_normSq_harmonicNonRough_activeFinalShell_le_receiver :
    ∀ᶠ x : ℝ in atTop, ∀ W : ℝ, 1 ≤ W → W ≤ x →
      ∀ (Q₀ : ℝ) (P₀ : Finset ℕ), (∀ p ∈ P₀, p.Prime) →
      (∀ p ∈ P₀, Q₀ < (p : ℝ)) →
      Disjoint P₀ (menonFinalRangePrimes x) →
      ∀ (V : ℕ → ℝ) {E : Set ℝ}, MeasurableSet E → E ⊆ Set.Icc (-W) W →
      let P := maskedActivePrimes Q₀ (menonFinalRangePrimes x) (menonFinalRangeTopNat x)
      (∫ w in E,
        ‖logPoly (harmonicNonRoughMoebiusC P₀) (menonFinalRangeShell x) w‖ ^ 2) ≤
        4 * (menonFinalRangeLadderSteps x : ℝ) *
          ∑ j ∈ Finset.range (menonFinalRangeLadderSteps x),
            ((V j) ^ 2 * menonMaskedFinalReceiverCostEnvelope x W (volume.real E) j +
              (harmonicPrimeMass (geomBlock P
                (menonFinalRangeLadderBase x)
                (1 + menonFinalRangeLadderEta x) j)) ^ 2 *
                menonMaskedFinalReceiverCostEnvelope x W
                  (volume.real (menonHarmonicPrimeBlockLargeOn E
                    (geomBlock P (menonFinalRangeLadderBase x)
                      (1 + menonFinalRangeLadderEta x) j) (V j))) j) +
          18 * (Real.log x) ^ (-(8 : ℝ)) := by
  filter_upwards [eventually_menonFinalRangeLadder_basic,
    eventually_menonFinalRangePrimes_ladder_range,
    eventually_menonFinalRangeLadder_cofactor_endpoints,
    eventually_integral_menonFinalRange_subsetLadderDefectWithCoeff_le_four_log_rpow_neg_eight,
    eventually_integral_Icc_normSq_dominatedHarmonic_finalRangeRough_le_log_rpow_neg_eight,
    eventually_menonFinalReceiverProductCostVolume_le_explicit] with
      x hbasic hPrangeFull hendpoints hdefect hrough hcost
  intro W hW hWx Q₀ P₀ hP₀prime hP₀lower hdisj V E hEm hEs
  dsimp only
  rcases hbasic with ⟨hx, _, hQ, _, heta, hL⟩
  let P := maskedActivePrimes Q₀ (menonFinalRangePrimes x) (menonFinalRangeTopNat x)
  let c := harmonicNonRoughRamareCofactorCoeff P₀ P
  let M : ℕ → ℝ := fun j =>
    volume.real (menonHarmonicPrimeBlockLargeOn E
      (geomBlock P (menonFinalRangeLadderBase x)
        (1 + menonFinalRangeLadderEta x) j) (V j))
  have hPsub : P ⊆ menonFinalRangePrimes x := by
    exact maskedActivePrimes_subset Q₀ _ _
  have hPprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact menonFinalRangePrimes_prime x (hPsub hp)
  have hdisjActive : Disjoint P₀ P :=
    Disjoint.mono_right hPsub hdisj
  have hPrange : ∀ p ∈ P,
      menonFinalRangeLadderBase x < (p : ℝ) ∧
      (p : ℝ) ≤ menonFinalRangeLadderBase x *
        (1 + menonFinalRangeLadderEta x) ^ menonFinalRangeLadderSteps x := by
    intro p hp
    exact hPrangeFull p (hPsub hp)
  have hc : ∀ {m : ℕ}, 0 < m → ‖c m‖ ≤ 1 / (m : ℝ) := by
    intro m hm
    exact norm_harmonicNonRoughRamareCofactorCoeff_le_inv P₀ P hm
  have hbil :=
    setIntegral_normSq_harmonicRamareBilinearWithCoeff_le_external_thresholds_exactDefect
      c hc (P := P) (A₀ := ⌈x⌉₊) (B₀ := menonFinalRangeTopNat x)
      (L := menonFinalRangeLadderSteps x) (Q := menonFinalRangeLadderBase x)
      (eta := menonFinalRangeLadderEta x) (W := W) hQ heta hW hL
      hPprime hPrange V M
      (fun j hj => (hendpoints j hj).1) (fun j hj => (hendpoints j hj).2)
      hEm hEs (fun _ _ => le_rfl)
  have hdefectE :
      (∫ w in E,
        ‖harmonicLadderProductDefectWithCoeff P ⌈x⌉₊ (menonFinalRangeTopNat x)
          (menonFinalRangeLadderBase x) (menonFinalRangeLadderEta x)
          (menonFinalRangeLadderSteps x) c w‖ ^ 2) ≤
        4 * (Real.log x) ^ (-(8 : ℝ)) := by
    calc
      _ ≤ ∫ w in Set.Icc (-W) W,
          ‖harmonicLadderProductDefectWithCoeff P ⌈x⌉₊ (menonFinalRangeTopNat x)
            (menonFinalRangeLadderBase x) (menonFinalRangeLadderEta x)
            (menonFinalRangeLadderSteps x) c w‖ ^ 2 := by
        have hf := (continuous_harmonicLadderProductDefectWithCoeff P ⌈x⌉₊
          (menonFinalRangeTopNat x) (menonFinalRangeLadderBase x)
          (menonFinalRangeLadderEta x) (menonFinalRangeLadderSteps x) c).norm.pow 2
        exact MeasureTheory.setIntegral_mono_set hf.integrableOn_Icc
          (Filter.Eventually.of_forall fun _ => by positivity)
          (Filter.Eventually.of_forall hEs)
      _ ≤ _ := hdefect P hPsub c hc W hW hWx
  have hroughFull := hrough (harmonicNonRoughMoebiusC P₀)
    (norm_harmonicNonRoughMoebiusC_le P₀)
  have hroughE :
      (∫ w in E,
        ‖logPoly (harmonicNonRoughMoebiusC P₀)
          (menonFinalRangeHarmonicRoughSet x) w‖ ^ 2) ≤
        (Real.log x) ^ (-(8 : ℝ)) := by
    have hsub : E ⊆ Set.Icc (-x) x := by
      intro w hw
      have hw' := hEs hw
      exact ⟨by linarith [hw'.1], by linarith [hw'.2]⟩
    calc
      _ ≤ ∫ w in Set.Icc (-x) x,
          ‖logPoly (harmonicNonRoughMoebiusC P₀)
            (menonFinalRangeHarmonicRoughSet x) w‖ ^ 2 := by
        have hf := (continuous_logPoly (harmonicNonRoughMoebiusC P₀)
          (menonFinalRangeHarmonicRoughSet x)).norm.pow 2
        exact MeasureTheory.setIntegral_mono_set hf.integrableOn_Icc
          (Filter.Eventually.of_forall fun _ => by positivity)
          (Filter.Eventually.of_forall hsub)
      _ ≤ _ := hroughFull
  have hsplit := setIntegral_normSq_add_le
    (F := fun w => harmonicNonRoughRamareBilinear P₀ P (menonFinalRangeShell x) w)
    (G := fun w => logPoly (harmonicNonRoughMoebiusC P₀)
      (menonFinalRangeHarmonicRoughSet x) w)
    (E := E) (W := W)
    (by simpa only [harmonicNonRoughRamareBilinear_eq_withCoeff] using
      continuous_harmonicRamareBilinearWithCoeff P (menonFinalRangeShell x) c)
    (continuous_logPoly _ _) hEm hEs
  have hspos : ∀ n ∈ menonFinalRangeShell x, 0 < n := by
    intro n hn
    have hn' := (Finset.mem_Icc.mp hn).1
    have hceil : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr (lt_trans zero_lt_one hx)
    omega
  have hsB : ∀ n ∈ menonFinalRangeShell x, n ≤ menonFinalRangeTopNat x := by
    intro n hn
    exact (Finset.mem_Icc.mp hn).2
  have hexact : ∀ w : ℝ,
      logPoly (harmonicNonRoughMoebiusC P₀) (menonFinalRangeShell x) w =
        harmonicNonRoughRamareBilinear P₀ P (menonFinalRangeShell x) w +
          logPoly (harmonicNonRoughMoebiusC P₀)
            (menonFinalRangeHarmonicRoughSet x) w := by
    intro w
    rw [logPoly_harmonicNonRoughMoebius_eq_ramare_add_rough
      hP₀prime hPprime hdisjActive]
    have hroughEq := logPoly_harmonicNonRoughMoebius_activeRough_eq
      hP₀prime (fun p hp => menonFinalRangePrimes_prime x hp) hdisj hP₀lower
      hspos hsB w
    simpa only [P, menonFinalRangeHarmonicRoughSet] using congrArg
      (fun z => harmonicNonRoughRamareBilinear P₀ P (menonFinalRangeShell x) w + z)
      hroughEq
  have hfull :
      (∫ w in E,
        ‖logPoly (harmonicNonRoughMoebiusC P₀) (menonFinalRangeShell x) w‖ ^ 2) ≤
      2 * (∫ w in E,
        ‖harmonicRamareBilinearWithCoeff P (menonFinalRangeShell x) c w‖ ^ 2) +
      2 * ∫ w in E,
        ‖logPoly (harmonicNonRoughMoebiusC P₀)
          (menonFinalRangeHarmonicRoughSet x) w‖ ^ 2 := by
    calc
      _ = ∫ w in E,
          ‖harmonicNonRoughRamareBilinear P₀ P (menonFinalRangeShell x) w +
            logPoly (harmonicNonRoughMoebiusC P₀)
              (menonFinalRangeHarmonicRoughSet x) w‖ ^ 2 := by
          exact MeasureTheory.setIntegral_congr_fun hEm fun w _ => by rw [hexact w]
      _ ≤ _ := by
        simpa only [P, c, harmonicNonRoughRamareBilinear_eq_withCoeff] using hsplit
  dsimp only [M] at hbil
  refine hfull.trans ?_
  have hassembled :
      2 * (∫ w in E,
        ‖harmonicRamareBilinearWithCoeff P (menonFinalRangeShell x) c w‖ ^ 2) +
      2 * ∫ w in E,
        ‖logPoly (harmonicNonRoughMoebiusC P₀)
          (menonFinalRangeHarmonicRoughSet x) w‖ ^ 2 ≤
      4 * (menonFinalRangeLadderSteps x : ℝ) *
        ∑ j ∈ Finset.range (menonFinalRangeLadderSteps x),
          (menonHarmonicProductCostVolume P ⌈x⌉₊ (menonFinalRangeTopNat x)
              (menonFinalRangeLadderBase x) (menonFinalRangeLadderEta x) W
              (V j) (volume.real E) j +
            menonHarmonicProductCostVolume P ⌈x⌉₊ (menonFinalRangeTopNat x)
              (menonFinalRangeLadderBase x) (menonFinalRangeLadderEta x) W
              (harmonicPrimeMass (geomBlock P (menonFinalRangeLadderBase x)
                (1 + menonFinalRangeLadderEta x) j))
              (volume.real (menonHarmonicPrimeBlockLargeOn E
                (geomBlock P (menonFinalRangeLadderBase x)
                  (1 + menonFinalRangeLadderEta x) j) (V j))) j) +
        18 * (Real.log x) ^ (-(8 : ℝ)) := by
    calc
      _ ≤ 2 * (2 * (menonFinalRangeLadderSteps x : ℝ) *
            ∑ j ∈ Finset.range (menonFinalRangeLadderSteps x),
              (menonHarmonicProductCostVolume P ⌈x⌉₊ (menonFinalRangeTopNat x)
                  (menonFinalRangeLadderBase x) (menonFinalRangeLadderEta x) W
                  (V j) (volume.real E) j +
                menonHarmonicProductCostVolume P ⌈x⌉₊ (menonFinalRangeTopNat x)
                  (menonFinalRangeLadderBase x) (menonFinalRangeLadderEta x) W
                  (harmonicPrimeMass (geomBlock P (menonFinalRangeLadderBase x)
                    (1 + menonFinalRangeLadderEta x) j))
                  (volume.real (menonHarmonicPrimeBlockLargeOn E
                    (geomBlock P (menonFinalRangeLadderBase x)
                      (1 + menonFinalRangeLadderEta x) j) (V j))) j) +
            2 * (4 * (Real.log x) ^ (-(8 : ℝ)))) +
          2 * (Real.log x) ^ (-(8 : ℝ)) := by
        have hbil' := hbil.trans
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hdefectE (by norm_num)))
        exact add_le_add (mul_le_mul_of_nonneg_left hbil' (by norm_num))
          (mul_le_mul_of_nonneg_left hroughE (by norm_num))
      _ = _ := by ring
  refine hassembled.trans ?_
  gcongr with j hj
  · simpa only [menonMaskedFinalReceiverCostEnvelope] using
      hcost W hW hWx P (V j) (volume.real E) j hj measureReal_nonneg
  · simpa only [menonMaskedFinalReceiverCostEnvelope] using
      hcost W hW hWx P
        (harmonicPrimeMass (geomBlock P (menonFinalRangeLadderBase x)
          (1 + menonFinalRangeLadderEta x) j))
        (volume.real (menonHarmonicPrimeBlockLargeOn E
          (geomBlock P (menonFinalRangeLadderBase x)
            (1 + menonFinalRangeLadderEta x) j) (V j))) j hj measureReal_nonneg

end

end RHTower.Sieve
