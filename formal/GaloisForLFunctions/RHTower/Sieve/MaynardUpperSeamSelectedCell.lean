import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellMiddleOverweight
import GaloisForLFunctions.RHTower.Sieve.MaynardLabelAbsorption

/-!
# Selected-cell Huxley closure of the high Route-T transition seam

At height ratio `mu >= 17/4`, the narrow scalar seam
`99/100 < mu * (1 - alpha) < 101/100` lies entirely in the middle amplitude strip.  Both literal
selected-cell branches then have far smaller Huxley exponents than the first Route-T receiver:
the adjacent branch is at most `2/3 + o(1)`, while the unique overweight branch is at most
`2 * (1 + mu/60) * (1 - alpha) + o(1)`.  This module records the resulting fixed power reserve.
-/

set_option maxRecDepth 10000

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- The adjacent-power Huxley exponent has a fixed gap below the first receiver on the high seam.
The amplitude lower bound needed by the analytic theorem follows from the seam itself. -/
theorem routeT_upper_seam_adjacent_exponent_le_first
    {mu alpha : ℝ} (hmuLo : 17 / 4 ≤ mu)
    (halphaHi : alpha ≤ 997 / 1000)
    (hseam : 99 / 100 < mu * (1 - alpha) ∧
      mu * (1 - alpha) < 101 / 100) :
    19 / 25 ≤ alpha ∧
      2 * (1 - maynardMiddleReferenceAmplitude alpha) /
          maynardMiddleReferenceAmplitude alpha +
          maynardLongGlobalAmplitudeDeficit / 100000 ≤
        mu * (1 - alpha) - 1 / 100 := by
  let d : ℝ := maynardLongGlobalAmplitudeDeficit
  let alpha0 : ℝ := maynardMiddleReferenceAmplitude alpha
  have hdsmall : d < (1 / 1000000 : ℝ) :=
    maynardLongGlobalAmplitudeDeficit_lt_one_millionth
  have hdelta : 0 ≤ 1 - alpha := by linarith
  have hscaled := mul_le_mul_of_nonneg_right hmuLo hdelta
  have halphaLo : 19 / 25 ≤ alpha := by nlinarith [hscaled, hseam.2]
  refine ⟨halphaLo, ?_⟩
  have ha0Range := maynardMiddleReferenceAmplitude_range halphaLo halphaHi
  have ha0pos : 0 < alpha0 := lt_of_lt_of_le (by norm_num) ha0Range.1
  have hcap : 2 * (1 - alpha0) / alpha0 ≤ 2 / 3 := by
    rw [div_le_iff₀ ha0pos]
    nlinarith [ha0Range.1]
  dsimp only [alpha0, d] at hcap hdsmall ⊢
  nlinarith [hseam.1]

/-- The literal overweight selected cell also has a fixed gap below the first receiver on the
high seam. -/
theorem routeT_upper_seam_overweight_exponent_le_first
    {mu alpha beta : ℝ} (hmuLo : 17 / 4 ≤ mu)
    (halphaHi : alpha ≤ 997 / 1000)
    (hbetaHi : beta ≤ 1 + mu / 60)
    (hseam : 99 / 100 < mu * (1 - alpha) ∧
      mu * (1 - alpha) < 101 / 100) :
    beta * (2 - 2 * alpha) + maynardLongGlobalAmplitudeDeficit / 100000 ≤
      mu * (1 - alpha) - 1 / 100 := by
  let d : ℝ := maynardLongGlobalAmplitudeDeficit
  let delta : ℝ := 1 - alpha
  have hdsmall : d < (1 / 1000000 : ℝ) :=
    maynardLongGlobalAmplitudeDeficit_lt_one_millionth
  have hdelta : 0 ≤ delta := by dsimp only [delta]; linarith
  have hmuScaled := mul_le_mul_of_nonneg_right hmuLo hdelta
  have hbetaScaled : beta * (2 * delta) ≤ (1 + mu / 60) * (2 * delta) :=
    mul_le_mul_of_nonneg_right hbetaHi (by positivity)
  dsimp only [delta, d] at hmuScaled hbetaScaled hdsmall ⊢
  nlinarith [hseam.1, hseam.2]

/-- A first-derivative `N/T` saving at maximal length `N = T^mu`, even with an arbitrarily small
power cost `T^eps`, has local Maynard amplitude `1 - (1-eps)/mu`. -/
theorem routeT_kuzminLandau_maximal_length_amplitude_identity
    {mu eps c : ℝ} :
    c + (1 - c - (1 - eps) / mu) = 1 - (1 - eps) / mu := by
  ring

/-- **Exact upper-seam selection obstruction.** At transition amplitude `1 - 1/mu`, the weighted
sub-height exclusion threshold produced by maximal-length Kuzmin--Landau lies strictly *above*
the transition, even if its power cost is zero.  Hence pointwise first-derivative saving cannot
force positive sub-height mass in the high phase; the surviving over-height boundary term must be
kept signed. -/
theorem routeT_kuzminLandau_subheight_exclusion_above_transition
    {mu eps E : ℝ} (hmu : 0 < mu) (hmuHi : mu ≤ 8)
    (heps : 0 ≤ eps) (hepsHi : eps ≤ 1) (hE : 0 ≤ E) :
    1 - 1 / mu <
      1 - ((1 - mu / 120) * ((1 - eps) / mu) - E) := by
  have ht : 0 < mu / 120 := by positivity
  have htHi : mu / 120 < 1 := by linarith
  have honeEps : 0 ≤ 1 - eps := by linarith
  have hprod : (1 - mu / 120) * (1 - eps) < 1 := by
    have hleft : 0 ≤ 1 - mu / 120 := by linarith
    have hmul : (1 - mu / 120) * (1 - eps) ≤
        (1 - mu / 120) * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) hleft
    linarith
  have hinv : 0 < mu⁻¹ := inv_pos.mpr hmu
  have hprodInv := mul_lt_mul_of_pos_right hprod hinv
  have hrewrite :
      (1 - mu / 120) * ((1 - eps) / mu) =
        ((1 - mu / 120) * (1 - eps)) * mu⁻¹ := by
    rw [div_eq_mul_inv]
    ring
  rw [hrewrite, div_eq_mul_inv]
  linarith

/-- Every fixed-label selected-cell fibre on the high transition seam satisfies the first Route-T
receiver with a fixed `1/100` exponent reserve. -/
theorem eventually_maynardWindowRelevantSelectedCell_upper_seam_fibre_first :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      17 / 4 ≤ mu → mu ≤ 8 →
      1 / 2 ≤ c → alpha ≤ 997 / 1000 →
      0 < delta →
      99 / 100 < mu * (1 - alpha) →
      mu * (1 - alpha) < 101 / 100 →
      ∀ (label : HeathBrownSelectionLabel L X 60),
      ∀ (S : Finset ℕ), S.Nonempty → S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      (∀ r ∈ S, IsMaynardWindowRelevantSelectedCell
        L X T mu N0 c (lam r) alpha label) →
      (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
        T ^ (mu * (1 - alpha) - 1 / 100) := by
  filter_upwards [eventually_maynardWindowRelevantSelectedCell_middle_adjacent_count,
    eventually_maynardWindowRelevantSelectedCell_middle_overweight_count,
    eventually_gt_atTop (1 : ℝ)] with T hadj hover hT
  intro L X K mu N0 c alpha delta hmuLo hmuHi hc halphaHi hdelta
    hseamLo hseamHi label S hSne hS lam hgap hband hselection
  let beta : ℝ := maynardSubHeightSelectedExponent T label
  have hmuBase : 4 / 3 ≤ mu := by linarith
  have hseam : 99 / 100 < mu * (1 - alpha) ∧
      mu * (1 - alpha) < 101 / 100 := ⟨hseamLo, hseamHi⟩
  have hscalar := routeT_upper_seam_adjacent_exponent_le_first
    hmuLo halphaHi hseam
  have halphaLo : 19 / 25 ≤ alpha := hscalar.1
  have hHF0 : 0 ≤ maynardHarmonicFactor K delta :=
    (maynardHarmonicFactor_pos K hdelta).le
  by_cases hbetaOne : beta < 1
  · have hraw := hadj hmuBase hmuHi hc halphaLo halphaHi hdelta label
      (by simpa only [beta] using hbetaOne) S hSne hS lam hgap hband hselection
    have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hscalar.2
    exact hraw.trans (mul_le_mul_of_nonneg_left hpow hHF0)
  · have hbetaLo : 1 ≤ beta := le_of_not_gt hbetaOne
    have hraw := hover hmuBase hmuHi hc halphaLo halphaHi hdelta label
      (by simpa only [beta] using hbetaLo) S hSne hS lam hgap hband hselection
    obtain ⟨r0, hr0⟩ := hSne
    rcases hselection r0 hr0 with
      ⟨_helig, _hrel, _hcore, _hune, _husub, _hbetaT, hbetaUpper,
        _hlength, _hlarge, _hbranch⟩
    have hbetaHi : beta ≤ 1 + mu / 60 := by
      have hbetaUpper' : beta < 1 + 2 * (mu / 120) := by
        simpa only [beta] using hbetaUpper
      linarith
    have hexp := routeT_upper_seam_overweight_exponent_le_first
      hmuLo halphaHi hbetaHi hseam
    have hraw' : (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
        T ^ (beta * (2 - 2 * alpha) +
          maynardLongGlobalAmplitudeDeficit / 100000) := by
      simpa only [beta] using hraw
    have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hexp
    exact hraw'.trans (mul_le_mul_of_nonneg_left hpow hHF0)

/-- Label entropy remains polylogarithmic throughout the full low-ordinate range `mu <= 8`.
Compared with the historical `mu <= 19/9` bound, only the harmless fixed base in the `X` factor
changes from `6` to `17`. -/
theorem heathBrownSelectionLabel_sixty_polylog_bound_eight
    {T mu t : ℝ} (hT : 0 < T) (hlogT : 1 ≤ Real.log T)
    (hmu : mu ≤ 8) (ht : t = mu / 120)
    {X L : ℕ} (hX : 1 ≤ X) (hL : 1 ≤ L)
    (hXscale : (X : ℝ) ≤ T ^ mu) (hLscale : (L : ℝ) ≤ T ^ (2 * t)) :
    (Fintype.card (HeathBrownSelectionLabel L X 60) : ℝ) ≤
      (60 : ℝ) * (2 : ℝ) ^ 120 * (17 : ℝ) ^ 60 * (2 : ℝ) ^ 60 *
        (Real.log T) ^ 120 := by
  have hlogT0 : 0 ≤ Real.log T := by linarith
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hLpos : 0 < (L : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hlogX : Real.log X ≤ mu * Real.log T := by
    have h := Real.log_le_log hXpos hXscale
    rwa [Real.log_rpow hT] at h
  have hXlog : ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤ 17 * Real.log T := by
    have hnat := natLogTwo_add_one_cast_le hX
    have hmumul : mu * Real.log T ≤ (8 : ℝ) * Real.log T :=
      mul_le_mul_of_nonneg_right hmu hlogT0
    linarith
  have htwice : 2 * t = mu / 60 := by rw [ht]; ring
  have hlogL : Real.log L ≤ (mu / 60) * Real.log T := by
    have h := Real.log_le_log hLpos hLscale
    rw [Real.log_rpow hT, htwice] at h
    exact h
  have hLlog : ((Nat.log 2 L + 1 : ℕ) : ℝ) ≤ 2 * Real.log T := by
    have hnat := natLogTwo_add_one_cast_le hL
    have hmudiv : (mu / 60) * Real.log T ≤ (2 / 15 : ℝ) * Real.log T := by
      have hmudiv' : mu / 60 ≤ (2 / 15 : ℝ) := by linarith
      exact mul_le_mul_of_nonneg_right hmudiv' hlogT0
    linarith
  have hcardNat := card_heathBrownSelectionLabel_sixty_le L X
  have hcard : (Fintype.card (HeathBrownSelectionLabel L X 60) : ℝ) ≤
      (60 : ℝ) * ((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 60 *
        ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 60 * (2 : ℝ) ^ 120 := by
    exact_mod_cast hcardNat
  have hXpow := pow_le_pow_left₀ (Nat.cast_nonneg _) hXlog 60
  have hLpow := pow_le_pow_left₀ (Nat.cast_nonneg _) hLlog 60
  have hprod :
      ((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 60 *
          ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 60 ≤
        (17 * Real.log T) ^ 60 * (2 * Real.log T) ^ 60 := by
    calc
      ((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 60 *
            ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 60 ≤
          (17 * Real.log T) ^ 60 *
            ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 60 :=
        mul_le_mul_of_nonneg_right hXpow (pow_nonneg (Nat.cast_nonneg _) 60)
      _ ≤ (17 * Real.log T) ^ 60 * (2 * Real.log T) ^ 60 :=
        mul_le_mul_of_nonneg_left hLpow
          (pow_nonneg (mul_nonneg (by norm_num) hlogT0) 60)
  calc
    (Fintype.card (HeathBrownSelectionLabel L X 60) : ℝ) ≤
        (60 : ℝ) * ((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 60 *
          ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 60 * (2 : ℝ) ^ 120 := hcard
    _ ≤ (60 : ℝ) * (17 * Real.log T) ^ 60 *
          (2 * Real.log T) ^ 60 * (2 : ℝ) ^ 120 := by
      calc
        (60 : ℝ) * ((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 60 *
              ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 60 * (2 : ℝ) ^ 120 =
            ((60 : ℝ) * (2 : ℝ) ^ 120) *
              (((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 60 *
                ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 60) := by ring
        _ ≤ ((60 : ℝ) * (2 : ℝ) ^ 120) *
              ((17 * Real.log T) ^ 60 * (2 * Real.log T) ^ 60) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = (60 : ℝ) * (17 * Real.log T) ^ 60 *
              (2 * Real.log T) ^ 60 * (2 : ℝ) ^ 120 := by ring
    _ = (60 : ℝ) * (2 : ℝ) ^ 120 * (17 : ℝ) ^ 60 * (2 : ℝ) ^ 60 *
          (Real.log T) ^ 120 := by ring

def maynardUpperSeamLabelPolylogConstant : ℝ :=
  (60 : ℝ) * (2 : ℝ) ^ 120 * (17 : ℝ) ^ 60 * (2 : ℝ) ^ 60

theorem maynardUpperSeamLabelPolylogConstant_pos :
    0 < maynardUpperSeamLabelPolylogConstant := by
  dsimp only [maynardUpperSeamLabelPolylogConstant]
  positivity

/-- **Global high-seam selected-cell bound.** Any literal selected-cell coloring at
`17/4 <= mu <= 8` satisfies the first Route-T receiver with a fixed `1/200` exponent reserve.
This theorem includes every label, the unique overweight cell, and full label entropy. -/
theorem eventually_card_le_maynard_first_of_selected_cell_coloring_upper_seam :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      1 ≤ X → 1 ≤ L →
      (X : ℝ) ≤ T ^ mu → (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      17 / 4 ≤ mu → mu ≤ 8 →
      1 / 2 ≤ c → alpha ≤ 997 / 1000 →
      0 < delta →
      99 / 100 < mu * (1 - alpha) →
      mu * (1 - alpha) < 101 / 100 →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      ∀ (color : ℕ → HeathBrownSelectionLabel L X 60),
      (∀ r ∈ S, IsMaynardWindowRelevantSelectedCell
        L X T mu N0 c (lam r) alpha (color r)) →
      (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
        T ^ (mu * (1 - alpha) - 1 / 200) := by
  filter_upwards [
    eventually_maynardWindowRelevantSelectedCell_upper_seam_fibre_first,
    eventually_maynardMiddleFixedLogCost_absorbed maynardUpperSeamLabelPolylogConstant
      maynardUpperSeamLabelPolylogConstant_pos 120 4000 (by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with T hfibre hlabelCost hlogT hT
  intro L X K mu N0 c alpha delta hX hL hXscale hLscale hmuLo hmuHi hc
    halphaHi hdelta hseamLo hseamHi S hS lam hgap hband color hcolor
  classical
  let d : ℝ := maynardLongGlobalAmplitudeDeficit
  let nlabels : ℝ := Fintype.card (HeathBrownSelectionLabel L X 60)
  let B : ℝ := maynardHarmonicFactor K delta *
    T ^ (mu * (1 - alpha) - 1 / 100)
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hlabel := heathBrownSelectionLabel_sixty_polylog_bound_eight
    hT0 hlogT hmuHi (by rfl : mu / 120 = mu / 120)
      hX hL hXscale hLscale
  have hlabelRaw : nlabels ≤
      maynardUpperSeamLabelPolylogConstant * (Real.log T) ^ 120 := by
    simpa only [nlabels, maynardUpperSeamLabelPolylogConstant] using hlabel
  have hlabelAbsorbedRaw := hlabelCost 1 0 (by norm_num)
    (by exact_mod_cast one_le_pow₀ (n := 90) hT.le)
    (by omega : 0 ≤ maynardMontgomeryFixedPolylogExponentBound)
  have hlabelAbsorbed :
      maynardUpperSeamLabelPolylogConstant * (Real.log T) ^ 120 ≤
        T ^ (d / 4000) := by
    norm_num [d] at hlabelAbsorbedRaw ⊢
    exact hlabelAbsorbedRaw
  have hnlabels : nlabels ≤ T ^ (d / 4000) :=
    hlabelRaw.trans hlabelAbsorbed
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (maynardHarmonicFactor_pos K hdelta).le
      (Real.rpow_nonneg hT0.le _)
  have hfibres : ∀ label : HeathBrownSelectionLabel L X 60,
      (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤ B := by
    intro label
    let Sf : Finset ℕ := S.filter fun r => color r = label
    by_cases hSf : Sf.Nonempty
    · have hSfS : Sf ⊆ S := Finset.filter_subset _ _
      have hSfRange : Sf ⊆ Finset.range K := hSfS.trans hS
      have hSfBand : ∀ r ∈ Sf, T ≤ lam r ∧ lam r ≤ 2 * T := by
        intro r hr
        exact hband r (hSfS hr)
      have hSfSelection : ∀ r ∈ Sf,
          IsMaynardWindowRelevantSelectedCell
            L X T mu N0 c (lam r) alpha label := by
        intro r hr
        have hrS := hSfS hr
        have hrcolor : color r = label := (Finset.mem_filter.mp hr).2
        simpa only [hrcolor] using hcolor r hrS
      have hbound := hfibre hmuLo hmuHi hc halphaHi hdelta hseamLo hseamHi
        label Sf hSf hSfRange lam hgap hSfBand hSfSelection
      simpa only [Sf, B] using hbound
    · have hzero : Sf.card = 0 :=
        Finset.card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hSf)
      simpa only [Sf, hzero, Nat.cast_zero] using hB0
  have hcardCast : (S.card : ℝ) =
      ∑ label : HeathBrownSelectionLabel L X 60,
        (((S.filter fun r => color r = label).card : ℕ) : ℝ) := by
    exact_mod_cast card_eq_sum_color_fibres S color
  have hsum : (S.card : ℝ) ≤ nlabels * B := by
    rw [hcardCast]
    calc
      ∑ label : HeathBrownSelectionLabel L X 60,
          (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤
          ∑ _label : HeathBrownSelectionLabel L X 60, B :=
        Finset.sum_le_sum fun label _ => hfibres label
      _ = nlabels * B := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hlabelMul : nlabels * B ≤ T ^ (d / 4000) * B :=
    mul_le_mul_of_nonneg_right hnlabels hB0
  have hdsmall : d < (1 / 1000000 : ℝ) :=
    maynardLongGlobalAmplitudeDeficit_lt_one_millionth
  have hexp : d / 4000 + (mu * (1 - alpha) - 1 / 100) ≤
      mu * (1 - alpha) - 1 / 200 := by nlinarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hexp
  calc
    (S.card : ℝ) ≤ nlabels * B := hsum
    _ ≤ T ^ (d / 4000) * B := hlabelMul
    _ = maynardHarmonicFactor K delta *
        T ^ (d / 4000 + (mu * (1 - alpha) - 1 / 100)) := by
      dsimp only [B]
      rw [show T ^ (d / 4000) *
          (maynardHarmonicFactor K delta *
            T ^ (mu * (1 - alpha) - 1 / 100)) =
          maynardHarmonicFactor K delta *
            (T ^ (d / 4000) * T ^ (mu * (1 - alpha) - 1 / 100)) by ring,
        ← Real.rpow_add hT0]
    _ ≤ maynardHarmonicFactor K delta *
        T ^ (mu * (1 - alpha) - 1 / 200) :=
      mul_le_mul_of_nonneg_left hpow (maynardHarmonicFactor_pos K hdelta).le

end RHTower.Sieve
