import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicDominatedRamareLadder
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicReceiverHeightProduct

/-!
# Receiver-height assembly for the initial-range non-rough projection

This is Menon's second Ramaré range applied to the exact polynomial retained by the first range.
The initial mask changes neither final prime blocks nor any numerical product cost.  Masked
cofactors and the masked final rough remainder are both dominated by the original reciprocal
harmonic coefficients, so the full final schedule closes with the same logarithmic budgets.
-/

namespace RHTower.Sieve

open Filter Finset MeasureTheory Topology

noncomputable section

/-- A coefficient dominated by the harmonic Möbius coefficient has the same final-rough energy
majorant. -/
theorem integral_Icc_normSq_dominatedHarmonic_finalRangeRough_le
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ ‖harmonicMoebiusC n‖)
    (x : ℝ) (hx : 1 ≤ x) :
    (∫ w in Set.Icc (-x) x,
      ‖logPoly c (menonFinalRangeHarmonicRoughSet x) w‖ ^ 2) ≤
      (5 * Real.pi / 2 * x +
        5 * Real.exp 1 / 2 * (menonFinalRangeTopNat x : ℝ)) *
          (((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
            (menonFinalRangeTopNat x)).card : ℝ) / x ^ 2) := by
  have henergy :
      ∑ n ∈ menonFinalRangeHarmonicRoughSet x, ‖c n‖ ^ 2 ≤
        ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
          (menonFinalRangeTopNat x)).card : ℝ) / x ^ 2 := by
    refine (Finset.sum_le_sum fun n _ => ?_).trans
      (sum_normSq_harmonicMoebiusC_menonFinalRangeHarmonicRoughSet_le x hx)
    exact pow_le_pow_left₀ (norm_nonneg _) (hc n) 2
  refine (integral_Icc_normSq_logPoly_le_energy c
    (M := menonFinalRangeTopNat x) ?_ ?_ hx).trans ?_
  · intro hzero
    rw [menonFinalRangeHarmonicRoughSet, Finset.mem_filter] at hzero
    have hshell := hzero.1
    rw [menonFinalRangeShell, Finset.mem_Icc] at hshell
    have hxceil : 1 ≤ ⌈x⌉₊ := by exact_mod_cast hx.trans (Nat.le_ceil x)
    omega
  · intro n hn
    rw [menonFinalRangeHarmonicRoughSet, Finset.mem_filter] at hn
    rw [menonFinalRangeShell, Finset.mem_Icc] at hn
    exact hn.1.2
  · exact mul_le_mul_of_nonneg_left henergy (by positivity)

/-- Uniform schedule form of the dominated final-rough estimate. -/
theorem eventually_integral_Icc_normSq_dominatedHarmonic_finalRangeRough_le_log_rpow_neg_eight :
    ∀ᶠ x : ℝ in atTop, ∀ (c : ℕ → ℂ),
      (∀ n, ‖c n‖ ≤ ‖harmonicMoebiusC n‖) →
      (∫ w in Set.Icc (-x) x,
        ‖logPoly c (menonFinalRangeHarmonicRoughSet x) w‖ ^ 2) ≤
          (Real.log x) ^ (-(8 : ℝ)) := by
  let C : ℝ := 5 * Real.pi / 2 + 15 * Real.exp 1 / 2
  have hlim :=
    tendsto_card_squarefreeSmoothUpTo_menonFinalRange_mul_logPow_div_zero.const_mul C
  simp only [mul_zero] at hlim
  have hsmall : ∀ᶠ x : ℝ in atTop,
      C * (((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
        (menonFinalRangeTopNat x)).card : ℝ) * (Real.log x) ^ 10 / x) < 1 :=
    (tendsto_order.1 hlim).2 1 zero_lt_one
  filter_upwards [hsmall, eventually_gt_atTop (Real.exp 1)] with x hsmall hxexp
  intro c hc
  have he1 : (1 : ℝ) < Real.exp 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hx1 : 1 < x := he1.trans hxexp
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hlog0 : 0 < Real.log x := Real.log_pos hx1
  have hlog1 : 1 < Real.log x :=
    (Real.lt_log_iff_exp_lt (by positivity)).2 hxexp
  have htop : (menonFinalRangeTopNat x : ℝ) ≤ 3 * x := by
    rw [menonFinalRangeTopNat]
    exact Nat.floor_le (by positivity)
  have hbase := integral_Icc_normSq_dominatedHarmonic_finalRangeRough_le c hc x hx1.le
  have hcoef : 5 * Real.pi / 2 * x +
      5 * Real.exp 1 / 2 * (menonFinalRangeTopNat x : ℝ) ≤ C * x := by
    dsimp [C]
    have hexp0 : 0 ≤ 5 * Real.exp 1 / 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left htop hexp0]
  have hquot0 : 0 ≤ ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
      (menonFinalRangeTopNat x)).card : ℝ) / x ^ 2 := by positivity
  have hbound := hbase.trans (mul_le_mul_of_nonneg_right hcoef hquot0)
  have hlog8 : 0 ≤ (Real.log x) ^ (8 : ℕ) := pow_nonneg hlog0.le _
  have hscaled := mul_le_mul_of_nonneg_right hbound hlog8
  have hlogpow : (Real.log x) ^ 8 ≤ (Real.log x) ^ 10 := by
    nlinarith [sq_nonneg ((Real.log x) ^ 4 * (Real.log x - 1))]
  have hcard0 : 0 ≤ ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
      (menonFinalRangeTopNat x)).card : ℝ) := by positivity
  have hcardLog :
      ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
        (menonFinalRangeTopNat x)).card : ℝ) * (Real.log x) ^ 8 / x ≤
      ((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
        (menonFinalRangeTopNat x)).card : ℝ) * (Real.log x) ^ 10 / x := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlogpow hcard0) hx0.le
  have hscaledOne :
      (∫ w in Set.Icc (-x) x,
        ‖logPoly c (menonFinalRangeHarmonicRoughSet x) w‖ ^ 2) *
          (Real.log x) ^ 8 ≤ 1 := by
    refine hscaled.trans ?_
    calc
      (C * x * (((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
          (menonFinalRangeTopNat x)).card : ℝ) / x ^ 2)) * (Real.log x) ^ 8 =
        C * (((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
          (menonFinalRangeTopNat x)).card : ℝ) * (Real.log x) ^ 8 / x) := by
            field_simp [ne_of_gt hx0]
      _ ≤ C * (((squarefreeSmoothUpTo (menonFinalRangePrimeCutoffNat x)
          (menonFinalRangeTopNat x)).card : ℝ) * (Real.log x) ^ 10 / x) := by
            exact mul_le_mul_of_nonneg_left hcardLog (by dsimp [C]; positivity)
      _ ≤ 1 := hsmall.le
  have hpow0 : 0 < (Real.log x) ^ (8 : ℕ) := pow_pos hlog0 _
  have hrpow : (Real.log x) ^ (8 : ℝ) = (Real.log x) ^ (8 : ℕ) := by
    norm_num [Real.rpow_natCast]
  rw [Real.rpow_neg hlog0.le]
  rw [hrpow]
  rw [inv_eq_one_div, le_div_iff₀ hpow0]
  exact hscaledOne

/-- Initial non-rough harmonic coefficient is pointwise dominated by the original one. -/
theorem norm_harmonicNonRoughMoebiusC_le (P₀ : Finset ℕ) (n : ℕ) :
    ‖harmonicNonRoughMoebiusC P₀ n‖ ≤ ‖harmonicMoebiusC n‖ := by
  rw [harmonicNonRoughMoebiusC]
  split_ifs
  · simp
  · exact le_rfl

/-- Explicit scalar multiplying one final prime-block threshold at receiver height `W`. -/
def menonMaskedFinalReceiverCostEnvelope (x W volE : ℝ) (j : ℕ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    (24 * (6 +
      80000 * Real.sqrt W * Real.log x * (2 * Real.pi * volE) *
        (menonFinalRangeLadderBase x *
          (1 + menonFinalRangeLadderEta x) ^ j) / x +
      144 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * W))))

/-- Closed receiver-height assembly for the initial-range non-rough harmonic shell.  Final prime
large-value sets are unchanged, and all masked errors are discharged by uniform dominated
coefficient estimates. -/
theorem eventually_setIntegral_normSq_harmonicNonRough_finalRangeShell_le_receiver_explicitLargeVolumes :
    ∀ᶠ x : ℝ in atTop, ∀ W : ℝ, 1 ≤ W → W ≤ x →
      ∀ (P₀ : Finset ℕ), (∀ p ∈ P₀, p.Prime) →
      Disjoint P₀ (menonFinalRangePrimes x) →
      ∀ (V : ℕ → ℝ) {E : Set ℝ}, MeasurableSet E → E ⊆ Set.Icc (-W) W →
      (∫ w in E,
        ‖logPoly (harmonicNonRoughMoebiusC P₀) (menonFinalRangeShell x) w‖ ^ 2) ≤
        4 * (menonFinalRangeLadderSteps x : ℝ) *
          ∑ j ∈ Finset.range (menonFinalRangeLadderSteps x),
            ((V j) ^ 2 * menonMaskedFinalReceiverCostEnvelope x W (volume.real E) j +
              (harmonicPrimeMass (geomBlock (menonFinalRangePrimes x)
                (menonFinalRangeLadderBase x)
                (1 + menonFinalRangeLadderEta x) j)) ^ 2 *
                menonMaskedFinalReceiverCostEnvelope x W
                  (volume.real (menonHarmonicPrimeBlockLargeOn E
                    (geomBlock (menonFinalRangePrimes x) (menonFinalRangeLadderBase x)
                      (1 + menonFinalRangeLadderEta x) j) (V j))) j) +
          18 * (Real.log x) ^ (-(8 : ℝ)) := by
  filter_upwards [eventually_menonFinalRangeLadder_basic,
    eventually_menonFinalRangePrimes_ladder_range,
    eventually_menonFinalRangeLadder_cofactor_endpoints,
    eventually_integral_menonFinalRange_fullLadderDefectWithCoeff_le_four_log_rpow_neg_eight,
    eventually_integral_Icc_normSq_dominatedHarmonic_finalRangeRough_le_log_rpow_neg_eight,
    eventually_menonFinalReceiverProductCostVolume_le_explicit] with
      x hbasic hPrange hendpoints hdefect hrough hcost
  intro W hW hWx P₀ hP₀prime hdisj V E hEm hEs
  rcases hbasic with ⟨hx, _, hQ, _, heta, hL⟩
  let P := menonFinalRangePrimes x
  let c := harmonicNonRoughRamareCofactorCoeff P₀ P
  let M : ℕ → ℝ := fun j =>
    volume.real (menonHarmonicPrimeBlockLargeOn E
      (geomBlock P (menonFinalRangeLadderBase x)
        (1 + menonFinalRangeLadderEta x) j) (V j))
  have hc : ∀ {m : ℕ}, 0 < m → ‖c m‖ ≤ 1 / (m : ℝ) := by
    intro m hm
    exact norm_harmonicNonRoughRamareCofactorCoeff_le_inv P₀ P hm
  have hbil :=
    setIntegral_normSq_harmonicRamareBilinearWithCoeff_le_external_thresholds_exactDefect
      c hc (P := P) (A₀ := ⌈x⌉₊) (B₀ := menonFinalRangeTopNat x)
      (L := menonFinalRangeLadderSteps x) (Q := menonFinalRangeLadderBase x)
      (eta := menonFinalRangeLadderEta x) (W := W) hQ heta hW hL
      (fun p hp => menonFinalRangePrimes_prime x hp) hPrange V M
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
      _ ≤ _ := hdefect c hc W hW hWx
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
  have hfull :
      (∫ w in E,
        ‖logPoly (harmonicNonRoughMoebiusC P₀) (menonFinalRangeShell x) w‖ ^ 2) ≤
      2 * (∫ w in E,
        ‖harmonicRamareBilinearWithCoeff P (menonFinalRangeShell x) c w‖ ^ 2) +
      2 * ∫ w in E,
        ‖logPoly (harmonicNonRoughMoebiusC P₀)
          (menonFinalRangeHarmonicRoughSet x) w‖ ^ 2 := by
    have hexact := logPoly_harmonicNonRoughMoebius_eq_ramare_add_rough
      hP₀prime (fun p hp => menonFinalRangePrimes_prime x hp) hdisj
      (menonFinalRangeShell x)
    calc
      (∫ w in E,
        ‖logPoly (harmonicNonRoughMoebiusC P₀) (menonFinalRangeShell x) w‖ ^ 2) =
        ∫ w in E,
          ‖harmonicNonRoughRamareBilinear P₀ (menonFinalRangePrimes x)
              (menonFinalRangeShell x) w +
            logPoly (harmonicNonRoughMoebiusC P₀)
              (menonFinalRangeHarmonicRoughSet x) w‖ ^ 2 := by
          exact MeasureTheory.setIntegral_congr_fun hEm fun w _ => by
            rw [hexact w, menonFinalRangeHarmonicRoughSet]
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
  · simpa only [menonMaskedFinalReceiverCostEnvelope, P] using
      hcost W hW hWx P (V j) (volume.real E) j hj measureReal_nonneg
  · simpa only [menonMaskedFinalReceiverCostEnvelope, P] using
      hcost W hW hWx P
        (harmonicPrimeMass (geomBlock P (menonFinalRangeLadderBase x)
          (1 + menonFinalRangeLadderEta x) j))
        (volume.real (menonHarmonicPrimeBlockLargeOn E
          (geomBlock P (menonFinalRangeLadderBase x)
            (1 + menonFinalRangeLadderEta x) j) (V j))) j hj measureReal_nonneg

end

end RHTower.Sieve
