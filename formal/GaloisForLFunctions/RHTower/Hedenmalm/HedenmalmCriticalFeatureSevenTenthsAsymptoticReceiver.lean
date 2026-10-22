import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureSevenTenthsCanonicalCensus
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureTranslatedSourcePlemeljCovariance

/-!
# Asymptotic source gate for the seven-tenths HCF receiver

The seven-tenths split removes the fixed deep transverse band by Route T zero density.  In the
remaining shallow band, the reflected five-center HCF quantum is strong enough that even the old
`21 / 100` corrected-budget target has ample room.  This file closes all normalization, padding,
and epsilon bookkeeping for that hybrid.

The final hypotheses are literal pole--Gamma Plemelj covariance ceilings on the widened canonical
lattice.  Thus the only unproved input is a quantitative source estimate; no divisor packet,
deep-band count, or lower-order von-Mangoldt term remains in the premise.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The five-center canonical lattice still has only linear cardinality. -/
theorem card_criticalFeatureCanonicalFiveCenterLatticeWindow (n : ℕ) :
    (criticalFeatureCanonicalFiveCenterLatticeWindow n).card = 2 * n + 5 := by
  rw [criticalFeatureCanonicalFiveCenterLatticeWindow,
    card_criticalFeatureCanonicalLatticeWindow]
  omega

/-- Widening the canonical lattice by one center at either end remains `o(N)`. -/
theorem tendsto_card_criticalFeatureCanonicalFiveCenterLatticeWindow_div_zeroCount :
    Tendsto
      (fun n : ℕ =>
        ((criticalFeatureCanonicalFiveCenterLatticeWindow n).card : ℝ) /
          criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) := by
  have hmajor : Tendsto
      (fun n : ℕ =>
        2 * (((criticalFeatureCanonicalLatticeWindow n).card : ℝ) /
          criticalFeatureCanonicalZeroCount n))
      atTop (𝓝 0) := by
    simpa using
      tendsto_const_nhds.mul
        tendsto_card_criticalFeatureCanonicalLatticeWindow_div_zeroCount
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_criticalFeatureCanonicalZeroCount_pos] with n hN
    exact div_nonneg (Nat.cast_nonneg _) hN.le
  · filter_upwards [eventually_criticalFeatureCanonicalZeroCount_pos] with n hN
    rw [card_criticalFeatureCanonicalFiveCenterLatticeWindow,
      card_criticalFeatureCanonicalLatticeWindow]
    push_cast
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [show 2 * ((2 * (n : ℝ) + 3) / criticalFeatureCanonicalZeroCount n) =
        (2 * (2 * (n : ℝ) + 3)) / criticalFeatureCanonicalZeroCount n by ring]
    exact div_le_div_of_nonneg_right (by nlinarith) hN.le

/-- On the widened five-center window, corrected budget and source-only Plemelj covariance still
differ by `o(N)`. -/
theorem tendsto_canonicalFiveCenter_correctedBudget_sub_plemeljCovariance_div :
    Tendsto
      (fun n : ℕ =>
        (criticalFeaturePrimeGammaOffLineLatticeBudget
              (criticalFeatureCanonicalFiveCenterLatticeWindow n) -
            criticalFeaturePoleGammaPlemeljCovariance
              (criticalFeatureCanonicalFiveCenterLatticeWindow n)) /
          criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) :=
  tendsto_correctedBudget_sub_plemeljCovariance_div
    criticalFeatureCanonicalFiveCenterLatticeWindow criticalFeatureCanonicalZeroCount
    eventually_criticalFeatureCanonicalZeroCount_pos
    tendsto_card_criticalFeatureCanonicalFiveCenterLatticeWindow_div_zeroCount

/-- Every asymptotic ceiling transfers exactly between corrected and source-only budgets on the
five-center lattice. -/
theorem canonicalFiveCenter_correctedBudget_ceiling_iff_plemeljCovariance_ceiling
    (c : ℝ) :
    CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePrimeGammaOffLineLatticeBudget
          (criticalFeatureCanonicalFiveCenterLatticeWindow n)) c ↔
      CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePoleGammaPlemeljCovariance
          (criticalFeatureCanonicalFiveCenterLatticeWindow n)) c :=
  criticalFeatureCanonicalAsymptoticUpper_iff_of_sub_div_tendsto_zero
    tendsto_canonicalFiveCenter_correctedBudget_sub_plemeljCovariance_div

/-- A deliberately coarse rational lower bound for the reflected five-center charge.  This keeps
the asymptotic receiver independent of the charge's large exact denominator. -/
theorem fortyFourFifths_le_criticalFeatureShallowReflectedFiveCenterCharge :
    (44 / 5 : ℝ) ≤ criticalFeatureShallowReflectedFiveCenterCharge := by
  rw [criticalFeatureShallowReflectedFiveCenterCharge,
    criticalFeatureShallowDirectFiveCenterCharge]
  have hmain : (5 : ℝ) ≤ 23232 / 4225 := by norm_num
  have htail : (0 : ℝ) ≤ 32 / 221 := by norm_num
  nlinarith

/-- The old `21 / 100` source ceiling, together with the already-proved deep-band density-zero
law, forces the canonical 75% conclusion eventually. -/
theorem eventually_three_quarters_line_of_canonicalFiveCenter_plemelj_twentyOneHundred
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePoleGammaPlemeljCovariance
        (criticalFeatureCanonicalFiveCenterLatticeWindow n)) (21 / 100)) :
    ∀ᶠ n : ℕ in atTop,
      3 * criticalFeatureCanonicalZeroCount n / 4 ≤
        criticalFeatureCanonicalCriticalLineCount n := by
  have hcorrected : CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePrimeGammaOffLineLatticeBudget
        (criticalFeatureCanonicalFiveCenterLatticeWindow n)) (21 / 100) :=
    (canonicalFiveCenter_correctedBudget_ceiling_iff_plemeljCovariance_ceiling
      (21 / 100)).2 hsource
  have hbudget := hcorrected (1 / 100) (by norm_num)
  have hdeep : ∀ᶠ n : ℕ in atTop,
      ((criticalFeatureCanonicalDeepRightCopyPacket n).card : ℝ) /
          criticalFeatureCanonicalZeroCount n < 1 / 10 :=
    (tendsto_order.1
      tendsto_card_criticalFeatureCanonicalDeepRightCopyPacket_div_zeroCount).2
      (1 / 10) (by norm_num)
  filter_upwards [hbudget, hdeep, eventually_criticalFeatureCanonicalZeroCount_pos]
    with n hbudgetN hdeepN hN
  apply three_quarters_line_of_canonicalSevenTenthsFiveCenterBudget n
  have hdeepN' :
      ((criticalFeatureCanonicalDeepRightCopyPacket n).card : ℝ) <
        (1 / 10) * criticalFeatureCanonicalZeroCount n :=
    (div_lt_iff₀ hN).mp hdeepN
  have hQ : 0 < criticalFeatureShallowReflectedFiveCenterCharge :=
    criticalFeatureShallowReflectedFiveCenterCharge_pos
  have hInv : (1 / criticalFeatureShallowReflectedFiveCenterCharge : ℝ) ≤ 5 / 44 := by
    rw [div_le_iff₀ hQ]
    nlinarith [fortyFourFifths_le_criticalFeatureShallowReflectedFiveCenterCharge]
  have hbudgetN' :
      criticalFeaturePrimeGammaOffLineLatticeBudget
          (criticalFeatureCanonicalFiveCenterLatticeWindow n) ≤
        (11 / 50) * criticalFeatureCanonicalZeroCount n := by
    have hc : (21 / 100 : ℝ) + 1 / 100 = 11 / 50 := by norm_num
    rwa [hc] at hbudgetN
  have hscaled :
      (1 / criticalFeatureShallowReflectedFiveCenterCharge) *
          criticalFeaturePrimeGammaOffLineLatticeBudget
            (criticalFeatureCanonicalFiveCenterLatticeWindow n) ≤
        (1 / 40) * criticalFeatureCanonicalZeroCount n := by
    calc
      _ ≤ (5 / 44) * criticalFeaturePrimeGammaOffLineLatticeBudget
          (criticalFeatureCanonicalFiveCenterLatticeWindow n) :=
        mul_le_mul_of_nonneg_right hInv
          (primeGammaOffLineLatticeBudget_nonneg _)
      _ ≤ (5 / 44) * ((11 / 50) * criticalFeatureCanonicalZeroCount n) :=
        mul_le_mul_of_nonneg_left hbudgetN' (by norm_num)
      _ = (1 / 40) * criticalFeatureCanonicalZeroCount n := by ring
  nlinarith

/-- The stronger historical `4 / 25` source target is an immediate corollary of the new hybrid
gate. -/
theorem eventually_three_quarters_line_of_canonicalFiveCenter_plemelj_fourTwentyFive
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePoleGammaPlemeljCovariance
        (criticalFeatureCanonicalFiveCenterLatticeWindow n)) (4 / 25)) :
    ∀ᶠ n : ℕ in atTop,
      3 * criticalFeatureCanonicalZeroCount n / 4 ≤
        criticalFeatureCanonicalCriticalLineCount n := by
  apply eventually_three_quarters_line_of_canonicalFiveCenter_plemelj_twentyOneHundred
  intro eps heps
  have h := hsource (eps + 1 / 20) (by norm_num; linarith)
  filter_upwards [h] with n hn
  have heq : (4 / 25 : ℝ) + (eps + 1 / 20) = 21 / 100 + eps := by ring
  rw [heq] at hn
  exact hn

end

end RHTower
