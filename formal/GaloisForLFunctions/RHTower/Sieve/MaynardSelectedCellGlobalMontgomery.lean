import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellFibreMontgomery
import GaloisForLFunctions.RHTower.Sieve.MaynardLabelAbsorption

/-!
# Global lower-strip count from tuned Montgomery fibres

Every literal selected-cell colour has the same Route-T second-alternative bound in the lower
amplitude strip.  A fixed `T^(1/400)` reserve absorbs all degree-60 label entropy before the
colour fibres are summed and the positive label count is cancelled.
-/

set_option maxRecDepth 10000

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- Complete degree-60 label entropy costs at most `T^(1/400)`. -/
theorem eventually_maynardLabelCost_absorbed_four_hundred :
    ∀ᶠ T : ℝ in atTop,
      maynardLabelPolylogConstant * (Real.log T) ^ 120 ≤
        T ^ (1 / 400 : ℝ) := by
  let C : ℝ := maynardLabelPolylogConstant
  have hC : 0 < C := by
    dsimp only [C, maynardLabelPolylogConstant]
    positivity
  have heps : (0 : ℝ) < 1 / 400 := by norm_num
  have hlo := (_root_.isLittleO_log_rpow_rpow_atTop 120 heps).def
    (show (0 : ℝ) < 1 / (2 * C) by positivity)
  filter_upwards [hlo, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (0 : ℝ)] with T hsmall hlogT hT
  have hlog0 : 0 ≤ Real.log T := by linarith
  have hTpow : 0 < T ^ (1 / 400 : ℝ) := Real.rpow_pos_of_pos hT _
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ Real.log T ^ (120 : ℝ)),
    abs_of_nonneg hTpow.le] at hsmall
  have hlogpow : Real.log T ^ (120 : ℝ) = Real.log T ^ (120 : ℕ) :=
    Real.rpow_natCast _ _
  rw [hlogpow] at hsmall
  have hscaled := mul_le_mul_of_nonneg_left hsmall hC.le
  have hcancel : C * (1 / (2 * C)) = 1 / 2 := by
    field_simp [hC.ne']
  have hhalf : (1 / 2 : ℝ) * T ^ (1 / 400 : ℝ) ≤
      T ^ (1 / 400 : ℝ) := by nlinarith
  change C * Real.log T ^ 120 ≤ T ^ (1 / 400 : ℝ)
  calc
    C * Real.log T ^ 120 ≤ C * (1 / (2 * C) * T ^ (1 / 400 : ℝ)) := hscaled
    _ = (1 / 2 : ℝ) * T ^ (1 / 400 : ℝ) := by
      rw [← mul_assoc, hcancel]
    _ ≤ T ^ (1 / 400 : ℝ) := hhalf

/-- **Global lower-strip Route-T second alternative.** -/
theorem eventually_card_le_maynard_second_of_selected_cell_coloring_low_amplitude :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      1 ≤ X → 1 ≤ L →
      (X : ℝ) ≤ T ^ mu → (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      0 ≤ c → 3 / 4 ≤ alpha → alpha ≤ 19 / 25 →
      0 < delta → delta ≤ 2 * T →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      ∀ (color : ℕ → HeathBrownSelectionLabel L X 60),
      (∀ r ∈ S, IsMaynardWindowRelevantSelectedCell
        L X T mu N0 c (lam r) alpha (color r)) →
      (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
        T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - 1 / 200) := by
  filter_upwards [
    eventually_maynardWindowRelevantSelectedCell_scaled_fibre_second_of_low_amplitude,
    eventually_maynardLabelCost_absorbed_four_hundred,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with T hfibre hlabelCost hlogT hT
  intro L X K mu N0 c alpha delta hX hL hXscale hLscale hmuLo hmuHi hc
    halphaLo halphaHi hdelta hdeltaHi S hS lam hgap hband color hcolor
  classical
  let nlabels : ℝ := Fintype.card (HeathBrownSelectionLabel L X 60)
  let B : ℝ := maynardHarmonicFactor K delta *
    T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - 1 / 200)
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hnlabelsPos : 0 < nlabels := by
    dsimp only [nlabels]
    exact_mod_cast Fintype.card_pos_iff.mpr
      (nonempty_heathBrownSelectionLabel L X 60 (by norm_num))
  have hlabel := heathBrownSelectionLabel_sixty_polylog_bound
    hT0 hlogT hmuHi (by rfl : mu / 120 = mu / 120)
      hX hL hXscale hLscale
  have hlabelRaw : nlabels ≤
      maynardLabelPolylogConstant * (Real.log T) ^ 120 := by
    simpa only [nlabels, maynardLabelPolylogConstant] using hlabel
  have hnlabels : nlabels ≤ T ^ (1 / 400 : ℝ) :=
    hlabelRaw.trans hlabelCost
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (maynardHarmonicFactor_pos K hdelta).le
      (Real.rpow_nonneg hT0.le _)
  have hbound : ∀ label : HeathBrownSelectionLabel L X 60,
      nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤ B := by
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
      simpa only [Sf, B] using
        hfibre hmuLo hmuHi hc halphaLo halphaHi hdelta hdeltaHi
          nlabels hnlabelsPos.le hnlabels label Sf hSf hSfRange lam hgap
          hSfBand hSfSelection
    · have hzero : Sf.card = 0 :=
        Finset.card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hSf)
      simpa only [Sf, hzero, Nat.cast_zero, mul_zero] using hB0
  have hcardCast : (S.card : ℝ) =
      ∑ label : HeathBrownSelectionLabel L X 60,
        (((S.filter fun r => color r = label).card : ℕ) : ℝ) := by
    exact_mod_cast card_eq_sum_color_fibres S color
  have hsum : nlabels * (S.card : ℝ) ≤ nlabels * B := by
    rw [hcardCast, mul_sum]
    calc
      ∑ label : HeathBrownSelectionLabel L X 60,
          nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤
          ∑ _label : HeathBrownSelectionLabel L X 60, B :=
        Finset.sum_le_sum fun label _ => hbound label
      _ = nlabels * B := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simpa only [B] using (mul_le_mul_iff_right₀ hnlabelsPos).mp hsum

end RHTower.Sieve
