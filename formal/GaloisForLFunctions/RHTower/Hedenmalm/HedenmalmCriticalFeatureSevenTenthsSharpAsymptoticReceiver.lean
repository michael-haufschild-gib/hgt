import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureSevenTenthsAsymptoticReceiver
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureFirstOrderWindingAsymptotic

/-!
# Sharp asymptotic receiver for the seven-tenths HCF split

The reflected five-center shallow charge is at least `44 / 5`.  Combining that charge with the
exact shallow/deep census and density-zero of the deep packet sends any source-only Plemelj ceiling
`c` to the critical-line lower density `1 - 5c / 22`.

Consequently `11 / 10` is the sharp receiver threshold for a three-quarter asymptotic lower bound.
The historical `21 / 100` target would instead force the stronger lower density `419 / 440`.
This file is receiver algebra only; it does not prove a source-side Plemelj ceiling.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Quantitative five-center transfer: a Plemelj source ceiling `c N + o(N)` forces critical-line
multiplicity at least `(1 - 5c / 22) N - o(N)`. -/
theorem criticalFeatureCanonicalCriticalLineCount_lower_of_canonicalFiveCenter_plemelj
    (c : ℝ)
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePoleGammaPlemeljCovariance
        (criticalFeatureCanonicalFiveCenterLatticeWindow n)) c) :
    CriticalFeatureCanonicalAsymptoticLower
      criticalFeatureCanonicalCriticalLineCount (1 - 5 * c / 22) := by
  have hcorrected : CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePrimeGammaOffLineLatticeBudget
        (criticalFeatureCanonicalFiveCenterLatticeWindow n)) c :=
    (canonicalFiveCenter_correctedBudget_ceiling_iff_plemeljCovariance_ceiling c).2 hsource
  intro eps heps
  have hbudget := hcorrected eps heps
  have hdeep : ∀ᶠ n : ℕ in atTop,
      ((criticalFeatureCanonicalDeepRightCopyPacket n).card : ℝ) /
          criticalFeatureCanonicalZeroCount n < eps / 4 :=
    (tendsto_order.1
      tendsto_card_criticalFeatureCanonicalDeepRightCopyPacket_div_zeroCount).2
      (eps / 4) (by linarith)
  filter_upwards [hbudget, hdeep, eventually_criticalFeatureCanonicalZeroCount_pos]
    with n hbudgetN hdeepN hN
  have hdeepN' :
      ((criticalFeatureCanonicalDeepRightCopyPacket n).card : ℝ) <
        (eps / 4) * criticalFeatureCanonicalZeroCount n :=
    (div_lt_iff₀ hN).mp hdeepN
  have hcharge :=
    finite_strictRight_shallow_card_mul_reflectedFiveCenterCharge_le_offLineLatticeBudget
      (criticalFeatureCanonicalFiveCenterLatticeWindow n)
      (criticalFeatureCanonicalShallowRightCopyPacket n)
      (fun q hq => criticalFeatureCanonicalShallowRightCopyPacket_transverse_pos hq)
      (fun q hq => criticalFeatureCanonicalShallowRightCopyPacket_im_le_oneFifth hq)
      (fun q hq => criticalFeatureCanonicalShallowRightCopyPacket_fiveCenters hq)
  have hshallow_nonneg :
      0 ≤ ((criticalFeatureCanonicalShallowRightCopyPacket n).card : ℝ) :=
    Nat.cast_nonneg _
  have hcharge' :
      (44 / 5 : ℝ) * ((criticalFeatureCanonicalShallowRightCopyPacket n).card : ℝ) ≤
        criticalFeaturePrimeGammaOffLineLatticeBudget
          (criticalFeatureCanonicalFiveCenterLatticeWindow n) := by
    calc
      _ ≤ ((criticalFeatureCanonicalShallowRightCopyPacket n).card : ℝ) *
          criticalFeatureShallowReflectedFiveCenterCharge := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left
          fortyFourFifths_le_criticalFeatureShallowReflectedFiveCenterCharge
          hshallow_nonneg
      _ ≤ _ := hcharge
  have hcensus :=
    criticalFeatureCanonicalZeroCount_eq_criticalLine_add_two_mul_shallow_deep n
  nlinarith

/-- The exact reflected shallow charge improves the sufficient source threshold from the coarse
`11 / 10` to `criticalFeatureShallowReflectedFiveCenterCharge / 8`. -/
theorem elevenTenths_lt_criticalFeatureShallowReflectedFiveCenterCharge_div_eight :
    (11 / 10 : ℝ) < criticalFeatureShallowReflectedFiveCenterCharge / 8 := by
  norm_num [criticalFeatureShallowReflectedFiveCenterCharge,
    criticalFeatureShallowDirectFiveCenterCharge]

/-- Exact-charge receiver.  No rational weakening of the five-center local quantum is used. -/
theorem criticalFeatureCanonicalCriticalLineCount_threeQuarters_lower_of_canonicalFiveCenter_plemelj_exactCharge
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePoleGammaPlemeljCovariance
        (criticalFeatureCanonicalFiveCenterLatticeWindow n))
      (criticalFeatureShallowReflectedFiveCenterCharge / 8)) :
    CriticalFeatureCanonicalAsymptoticLower
      criticalFeatureCanonicalCriticalLineCount (3 / 4) := by
  have hcorrected : CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePrimeGammaOffLineLatticeBudget
        (criticalFeatureCanonicalFiveCenterLatticeWindow n))
      (criticalFeatureShallowReflectedFiveCenterCharge / 8) :=
    (canonicalFiveCenter_correctedBudget_ceiling_iff_plemeljCovariance_ceiling
      (criticalFeatureShallowReflectedFiveCenterCharge / 8)).2 hsource
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
    finite_strictRight_shallow_card_mul_reflectedFiveCenterCharge_le_offLineLatticeBudget
      (criticalFeatureCanonicalFiveCenterLatticeWindow n)
      (criticalFeatureCanonicalShallowRightCopyPacket n)
      (fun q hq => criticalFeatureCanonicalShallowRightCopyPacket_transverse_pos hq)
      (fun q hq => criticalFeatureCanonicalShallowRightCopyPacket_im_le_oneFifth hq)
      (fun q hq => criticalFeatureCanonicalShallowRightCopyPacket_fiveCenters hq)
  have hcensus :=
    criticalFeatureCanonicalZeroCount_eq_criticalLine_add_two_mul_shallow_deep n
  norm_num [criticalFeatureShallowReflectedFiveCenterCharge,
    criticalFeatureShallowDirectFiveCenterCharge] at hbudgetN hcharge
  nlinarith

/-- Every strict source ceiling below the exact reflected-charge threshold gives the eventual
pointwise three-quarter inequality. -/
theorem eventually_three_quarters_line_of_canonicalFiveCenter_plemelj_of_lt_exactCharge
    {c : ℝ}
    (hc : c < criticalFeatureShallowReflectedFiveCenterCharge / 8)
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePoleGammaPlemeljCovariance
        (criticalFeatureCanonicalFiveCenterLatticeWindow n)) c) :
    ∀ᶠ n : ℕ in atTop,
      3 * criticalFeatureCanonicalZeroCount n / 4 ≤
        criticalFeatureCanonicalCriticalLineCount n := by
  have hcorrected : CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePrimeGammaOffLineLatticeBudget
        (criticalFeatureCanonicalFiveCenterLatticeWindow n)) c :=
    (canonicalFiveCenter_correctedBudget_ceiling_iff_plemeljCovariance_ceiling c).2 hsource
  let gap : ℝ := criticalFeatureShallowReflectedFiveCenterCharge / 8 - c
  have hgap : 0 < gap := by
    dsimp [gap]
    exact sub_pos.mpr hc
  have hQ : 0 < criticalFeatureShallowReflectedFiveCenterCharge :=
    criticalFeatureShallowReflectedFiveCenterCharge_pos
  have hbudget := hcorrected (gap / 4) (by linarith)
  have hdeepScale : 0 < gap / (4 * criticalFeatureShallowReflectedFiveCenterCharge) :=
    div_pos hgap (mul_pos (by norm_num) hQ)
  have hdeep : ∀ᶠ n : ℕ in atTop,
      ((criticalFeatureCanonicalDeepRightCopyPacket n).card : ℝ) /
          criticalFeatureCanonicalZeroCount n <
        gap / (4 * criticalFeatureShallowReflectedFiveCenterCharge) :=
    (tendsto_order.1
      tendsto_card_criticalFeatureCanonicalDeepRightCopyPacket_div_zeroCount).2
      _ hdeepScale
  filter_upwards [hbudget, hdeep, eventually_criticalFeatureCanonicalZeroCount_pos]
    with n hbudgetN hdeepN hN
  apply three_quarters_line_of_canonicalSevenTenthsFiveCenterBudget n
  have hdeepN' :
      ((criticalFeatureCanonicalDeepRightCopyPacket n).card : ℝ) <
        (gap / (4 * criticalFeatureShallowReflectedFiveCenterCharge)) *
          criticalFeatureCanonicalZeroCount n :=
    (div_lt_iff₀ hN).mp hdeepN
  have hscaled := mul_le_mul_of_nonneg_left hbudgetN
    (by positivity : 0 ≤ 1 / criticalFeatureShallowReflectedFiveCenterCharge)
  dsimp [gap] at hscaled hdeepN'
  norm_num [criticalFeatureShallowReflectedFiveCenterCharge,
    criticalFeatureShallowDirectFiveCenterCharge] at hscaled hdeepN' ⊢
  nlinarith

/-- Source ceiling `11 / 10` is sufficient for the asymptotic three-quarter theorem. -/
theorem criticalFeatureCanonicalCriticalLineCount_threeQuarters_lower_of_canonicalFiveCenter_plemelj_elevenTenths
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePoleGammaPlemeljCovariance
        (criticalFeatureCanonicalFiveCenterLatticeWindow n)) (11 / 10)) :
    CriticalFeatureCanonicalAsymptoticLower
      criticalFeatureCanonicalCriticalLineCount (3 / 4) := by
  simpa only [show (1 : ℝ) - 5 * (11 / 10) / 22 = 3 / 4 by norm_num] using
    criticalFeatureCanonicalCriticalLineCount_lower_of_canonicalFiveCenter_plemelj
      (11 / 10) hsource

/-- The historical `21 / 100` ceiling would force at least `419 / 440` of multiplicity onto the
critical line asymptotically, rather than merely three quarters. -/
theorem criticalFeatureCanonicalCriticalLineCount_fourHundredNineteenFourFortieths_lower_of_canonicalFiveCenter_plemelj_twentyOneHundred
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePoleGammaPlemeljCovariance
        (criticalFeatureCanonicalFiveCenterLatticeWindow n)) (21 / 100)) :
    CriticalFeatureCanonicalAsymptoticLower
      criticalFeatureCanonicalCriticalLineCount (419 / 440) := by
  simpa only [show (1 : ℝ) - 5 * (21 / 100) / 22 = 419 / 440 by norm_num] using
    criticalFeatureCanonicalCriticalLineCount_lower_of_canonicalFiveCenter_plemelj
      (21 / 100) hsource

/-- Any strict source ceiling below `11 / 10` leaves enough asymptotic slack for an eventual exact
three-quarter inequality. -/
theorem eventually_three_quarters_line_of_canonicalFiveCenter_plemelj_of_lt_elevenTenths
    {c : ℝ} (hc : c < 11 / 10)
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePoleGammaPlemeljCovariance
        (criticalFeatureCanonicalFiveCenterLatticeWindow n)) c) :
    ∀ᶠ n : ℕ in atTop,
      3 * criticalFeatureCanonicalZeroCount n / 4 ≤
        criticalFeatureCanonicalCriticalLineCount n := by
  let gap : ℝ := (1 - 5 * c / 22) - 3 / 4
  have hgap : 0 < gap := by
    dsimp [gap]
    nlinarith
  have hlower :=
    criticalFeatureCanonicalCriticalLineCount_lower_of_canonicalFiveCenter_plemelj
      c hsource (gap / 2) (by linarith)
  filter_upwards [hlower, eventually_criticalFeatureCanonicalZeroCount_pos]
    with n hlowerN hN
  dsimp [gap] at hlowerN
  nlinarith

end

end RHTower
