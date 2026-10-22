import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureSevenTenthsSevenCenterCharge
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureSevenTenthsAsymptoticReceiver
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureFirstOrderWindingAsymptotic

/-!
# Canonical seven-center HCF receiver

Widening the canonical lattice by two sites on each side retains the seven-center shallow charge
without changing the `o(N)` source replacement.  The resulting exact source threshold is strictly
larger than the five-center threshold.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Canonical height window padded for all offsets from `-3` through `3`. -/
def criticalFeatureCanonicalSevenCenterLatticeWindow (n : ℕ) : Finset ℤ :=
  criticalFeatureCanonicalLatticeWindow (n + 2)

theorem card_criticalFeatureCanonicalSevenCenterLatticeWindow (n : ℕ) :
    (criticalFeatureCanonicalSevenCenterLatticeWindow n).card = 2 * n + 7 := by
  rw [criticalFeatureCanonicalSevenCenterLatticeWindow,
    card_criticalFeatureCanonicalLatticeWindow]
  omega

/-- Every canonical shallow copy retains all seven nearest height centers. -/
theorem criticalFeatureCanonicalShallowRightCopyPacket_sevenCenters
    {n : ℕ} {q : XiZeroCopy}
    (hq : q ∈ criticalFeatureCanonicalShallowRightCopyPacket n) :
    ∀ j ∈ criticalFeatureSevenCenterStencil,
      round (xiSpectralPoint q).re + j ∈
        criticalFeatureCanonicalSevenCenterLatticeWindow n := by
  have hdata := mem_criticalFeatureCanonicalShallowRightCopyPacket.mp hq
  have hx : |(xiSpectralPoint q).re| ≤ (n : ℝ) := by
    simpa [xiSpectralPoint] using hdata.1
  have herr := HTGeometry.abs_sub_round_le_half (xiSpectralPoint q).re
  rw [abs_le] at hx herr
  have hupperReal : ((round (xiSpectralPoint q).re : ℤ) : ℝ) < n + 1 := by
    linarith [hx.2, herr.1]
  have hlowerReal : -(n : ℝ) - 1 < ((round (xiSpectralPoint q).re : ℤ) : ℝ) := by
    linarith [hx.1, herr.2]
  have hupperInt : round (xiSpectralPoint q).re < (n : ℤ) + 1 := by
    exact_mod_cast hupperReal
  have hlowerInt : -(n : ℤ) - 1 < round (xiSpectralPoint q).re := by
    exact_mod_cast hlowerReal
  have hroundUpper : round (xiSpectralPoint q).re ≤ (n : ℤ) := by omega
  have hroundLower : -(n : ℤ) ≤ round (xiSpectralPoint q).re := by omega
  intro j hj
  have hj' : j = -3 ∨ j = -2 ∨ j = -1 ∨ j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
    simpa [criticalFeatureSevenCenterStencil] using hj
  simp only [criticalFeatureCanonicalSevenCenterLatticeWindow,
    criticalFeatureCanonicalLatticeWindow, Finset.mem_Icc]
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- Pointwise seven-center receiver with only corrected source budget and deep count remaining. -/
theorem three_quarters_line_of_canonicalSevenTenthsSevenCenterBudget
    (n : ℕ)
    (hbudget :
      (1 / criticalFeatureShallowReflectedSevenCenterCharge) *
          criticalFeaturePrimeGammaOffLineLatticeBudget
            (criticalFeatureCanonicalSevenCenterLatticeWindow n) +
        ((criticalFeatureCanonicalDeepRightCopyPacket n).card : ℝ) ≤
          criticalFeatureCanonicalZeroCount n / 8) :
    3 * criticalFeatureCanonicalZeroCount n / 4 ≤
      criticalFeatureCanonicalCriticalLineCount n := by
  have hcharge :=
    finite_strictRight_shallow_card_mul_reflectedSevenCenterCharge_le_offLineLatticeBudget
      (criticalFeatureCanonicalSevenCenterLatticeWindow n)
      (criticalFeatureCanonicalShallowRightCopyPacket n)
      (fun q hq => criticalFeatureCanonicalShallowRightCopyPacket_transverse_pos hq)
      (fun q hq => criticalFeatureCanonicalShallowRightCopyPacket_im_le_oneFifth hq)
      (fun q hq => criticalFeatureCanonicalShallowRightCopyPacket_sevenCenters hq)
  have hQ := criticalFeatureShallowReflectedSevenCenterCharge_pos
  have hshallowEnergy :
      ((criticalFeatureCanonicalShallowRightCopyPacket n).card : ℝ) ≤
        (1 / criticalFeatureShallowReflectedSevenCenterCharge) *
          criticalFeaturePrimeGammaOffLineLatticeBudget
            (criticalFeatureCanonicalSevenCenterLatticeWindow n) := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hQ]
    simpa [mul_comm] using hcharge
  exact three_quarters_line_of_shallowEnergy_and_deepCount
    (by
      rw [criticalFeatureCanonicalZeroCount]
      exact_mod_cast xiZeroCount_nonneg (n : ℝ))
    (criticalFeatureCanonicalZeroCount_eq_criticalLine_add_two_mul_shallow_deep n)
    hshallowEnergy hbudget

/-- Seven-center padding remains negligible against the canonical zero count. -/
theorem tendsto_card_criticalFeatureCanonicalSevenCenterLatticeWindow_div_zeroCount :
    Tendsto
      (fun n : ℕ =>
        ((criticalFeatureCanonicalSevenCenterLatticeWindow n).card : ℝ) /
          criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) := by
  have hmajor : Tendsto
      (fun n : ℕ =>
        3 * (((criticalFeatureCanonicalLatticeWindow n).card : ℝ) /
          criticalFeatureCanonicalZeroCount n))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      tendsto_card_criticalFeatureCanonicalLatticeWindow_div_zeroCount
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_criticalFeatureCanonicalZeroCount_pos] with n hN
    exact div_nonneg (Nat.cast_nonneg _) hN.le
  · filter_upwards [eventually_criticalFeatureCanonicalZeroCount_pos] with n hN
    rw [card_criticalFeatureCanonicalSevenCenterLatticeWindow,
      card_criticalFeatureCanonicalLatticeWindow]
    push_cast
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [show 3 * ((2 * (n : ℝ) + 3) / criticalFeatureCanonicalZeroCount n) =
        (3 * (2 * (n : ℝ) + 3)) / criticalFeatureCanonicalZeroCount n by ring]
    exact div_le_div_of_nonneg_right (by nlinarith) hN.le

/-- Corrected and Plemelj seven-center budgets differ by `o(N)`. -/
theorem tendsto_canonicalSevenCenter_correctedBudget_sub_plemeljCovariance_div :
    Tendsto
      (fun n : ℕ =>
        (criticalFeaturePrimeGammaOffLineLatticeBudget
              (criticalFeatureCanonicalSevenCenterLatticeWindow n) -
            criticalFeaturePoleGammaPlemeljCovariance
              (criticalFeatureCanonicalSevenCenterLatticeWindow n)) /
          criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) :=
  tendsto_correctedBudget_sub_plemeljCovariance_div
    criticalFeatureCanonicalSevenCenterLatticeWindow criticalFeatureCanonicalZeroCount
    eventually_criticalFeatureCanonicalZeroCount_pos
    tendsto_card_criticalFeatureCanonicalSevenCenterLatticeWindow_div_zeroCount

/-- Every asymptotic ceiling transfers between corrected and source-only seven-center budgets. -/
theorem canonicalSevenCenter_correctedBudget_ceiling_iff_plemeljCovariance_ceiling
    (c : ℝ) :
    CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePrimeGammaOffLineLatticeBudget
          (criticalFeatureCanonicalSevenCenterLatticeWindow n)) c ↔
      CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePoleGammaPlemeljCovariance
          (criticalFeatureCanonicalSevenCenterLatticeWindow n)) c :=
  criticalFeatureCanonicalAsymptoticUpper_iff_of_sub_div_tendsto_zero
    tendsto_canonicalSevenCenter_correctedBudget_sub_plemeljCovariance_div

/-- Retaining displacement-three channels strictly raises the exact sufficient source ceiling. -/
theorem criticalFeatureShallowReflectedFiveCenterCharge_div_eight_lt_sevenCenter :
    criticalFeatureShallowReflectedFiveCenterCharge / 8 <
      criticalFeatureShallowReflectedSevenCenterCharge / 8 := by
  norm_num [criticalFeatureShallowReflectedFiveCenterCharge,
    criticalFeatureShallowDirectFiveCenterCharge,
    criticalFeatureShallowReflectedSevenCenterCharge,
    criticalFeatureShallowDirectSevenCenterCharge]

/-- Exact seven-center source threshold for the asymptotic three-quarter theorem. -/
theorem criticalFeatureCanonicalCriticalLineCount_threeQuarters_lower_of_canonicalSevenCenter_plemelj_exactCharge
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePoleGammaPlemeljCovariance
        (criticalFeatureCanonicalSevenCenterLatticeWindow n))
      (criticalFeatureShallowReflectedSevenCenterCharge / 8)) :
    CriticalFeatureCanonicalAsymptoticLower
      criticalFeatureCanonicalCriticalLineCount (3 / 4) := by
  have hcorrected : CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePrimeGammaOffLineLatticeBudget
        (criticalFeatureCanonicalSevenCenterLatticeWindow n))
      (criticalFeatureShallowReflectedSevenCenterCharge / 8) :=
    (canonicalSevenCenter_correctedBudget_ceiling_iff_plemeljCovariance_ceiling
      (criticalFeatureShallowReflectedSevenCenterCharge / 8)).2 hsource
  intro eps heps
  have hbudget := hcorrected (eps / 4) (by linarith)
  have hdeep : ∀ᶠ n : ℕ in atTop,
      ((criticalFeatureCanonicalDeepRightCopyPacket n).card : ℝ) /
          criticalFeatureCanonicalZeroCount n < eps / 8 :=
    (tendsto_order.1
      tendsto_card_criticalFeatureCanonicalDeepRightCopyPacket_div_zeroCount).2
      (eps / 8) (by linarith)
  filter_upwards [hbudget, hdeep, eventually_criticalFeatureCanonicalZeroCount_pos]
    with n hbudgetN hdeepN hN
  have hdeepN' :
      ((criticalFeatureCanonicalDeepRightCopyPacket n).card : ℝ) <
        (eps / 8) * criticalFeatureCanonicalZeroCount n :=
    (div_lt_iff₀ hN).mp hdeepN
  have hcharge :=
    finite_strictRight_shallow_card_mul_reflectedSevenCenterCharge_le_offLineLatticeBudget
      (criticalFeatureCanonicalSevenCenterLatticeWindow n)
      (criticalFeatureCanonicalShallowRightCopyPacket n)
      (fun q hq => criticalFeatureCanonicalShallowRightCopyPacket_transverse_pos hq)
      (fun q hq => criticalFeatureCanonicalShallowRightCopyPacket_im_le_oneFifth hq)
      (fun q hq => criticalFeatureCanonicalShallowRightCopyPacket_sevenCenters hq)
  have hcensus :=
    criticalFeatureCanonicalZeroCount_eq_criticalLine_add_two_mul_shallow_deep n
  norm_num [criticalFeatureShallowReflectedSevenCenterCharge,
    criticalFeatureShallowDirectSevenCenterCharge] at hbudgetN hcharge
  nlinarith

/-- Every strict seven-center source ceiling below the exact charge threshold gives the eventual
pointwise three-quarter inequality. -/
theorem eventually_three_quarters_line_of_canonicalSevenCenter_plemelj_of_lt_exactCharge
    {c : ℝ}
    (hc : c < criticalFeatureShallowReflectedSevenCenterCharge / 8)
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePoleGammaPlemeljCovariance
        (criticalFeatureCanonicalSevenCenterLatticeWindow n)) c) :
    ∀ᶠ n : ℕ in atTop,
      3 * criticalFeatureCanonicalZeroCount n / 4 ≤
        criticalFeatureCanonicalCriticalLineCount n := by
  have hcorrected : CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePrimeGammaOffLineLatticeBudget
        (criticalFeatureCanonicalSevenCenterLatticeWindow n)) c :=
    (canonicalSevenCenter_correctedBudget_ceiling_iff_plemeljCovariance_ceiling c).2 hsource
  let gap : ℝ := criticalFeatureShallowReflectedSevenCenterCharge / 8 - c
  have hgap : 0 < gap := by
    dsimp [gap]
    exact sub_pos.mpr hc
  have hQ : 0 < criticalFeatureShallowReflectedSevenCenterCharge :=
    criticalFeatureShallowReflectedSevenCenterCharge_pos
  have hbudget := hcorrected (gap / 4) (by linarith)
  have hdeepScale : 0 < gap / (4 * criticalFeatureShallowReflectedSevenCenterCharge) :=
    div_pos hgap (mul_pos (by norm_num) hQ)
  have hdeep : ∀ᶠ n : ℕ in atTop,
      ((criticalFeatureCanonicalDeepRightCopyPacket n).card : ℝ) /
          criticalFeatureCanonicalZeroCount n <
        gap / (4 * criticalFeatureShallowReflectedSevenCenterCharge) :=
    (tendsto_order.1
      tendsto_card_criticalFeatureCanonicalDeepRightCopyPacket_div_zeroCount).2
      _ hdeepScale
  filter_upwards [hbudget, hdeep, eventually_criticalFeatureCanonicalZeroCount_pos]
    with n hbudgetN hdeepN hN
  apply three_quarters_line_of_canonicalSevenTenthsSevenCenterBudget n
  have hdeepN' :
      ((criticalFeatureCanonicalDeepRightCopyPacket n).card : ℝ) <
        (gap / (4 * criticalFeatureShallowReflectedSevenCenterCharge)) *
          criticalFeatureCanonicalZeroCount n :=
    (div_lt_iff₀ hN).mp hdeepN
  have hscaled := mul_le_mul_of_nonneg_left hbudgetN
    (by positivity : 0 ≤ 1 / criticalFeatureShallowReflectedSevenCenterCharge)
  dsimp [gap] at hscaled hdeepN'
  norm_num [criticalFeatureShallowReflectedSevenCenterCharge,
    criticalFeatureShallowDirectSevenCenterCharge] at hscaled hdeepN' ⊢
  nlinarith

end

end RHTower
