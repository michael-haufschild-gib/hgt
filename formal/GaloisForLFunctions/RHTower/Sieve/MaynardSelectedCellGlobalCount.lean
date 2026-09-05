import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellFibreCount
import GaloisForLFunctions.RHTower.Sieve.MaynardLabelAbsorption

/-!
# Global moving-endpoint count from literal selected-cell coloring

The moving endpoint reserve is divided before summation.  One half pays the optimizer-scale
energy and fixed polynomial factor inside every fibre; one half pays complete degree-`60` label
entropy.  Multiplying each fibre by the full number of labels before summing makes a mixture of
Maynard's two local alternatives harmless: all fibres are bounded by whichever global target is
larger, and the positive label count cancels after the finite sum.
-/

set_option maxRecDepth 10000

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- **Global exact Maynard dichotomy for literal selected-cell colors.** -/
theorem eventually_card_le_maynard_first_or_second_of_selected_cell_coloring (A : ℝ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      1 ≤ X → 1 ≤ L →
      (X : ℝ) ≤ T ^ mu → (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 / 2 ≤ c → 997 / 1000 < alpha →
      alpha ≤ 1 - routeTEndpointGlobalDeficit A T →
      0 < delta →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T) →
      ∀ (color : ℕ → HeathBrownSelectionLabel L X 60),
      (∀ r ∈ S, IsMaynardWindowRelevantSelectedCell
        L X T mu N0 c (lam r) alpha (color r)) →
      (S.card : ℝ) ≤
          maynardHarmonicFactor K delta *
            T ^ (mu * (1 - alpha) - routeTEndpointGlobalDeficit A T / 200) ∨
        (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
          T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) -
            routeTEndpointGlobalDeficit A T / 200) := by
  filter_upwards [
    eventually_maynardWindowRelevantSelectedCell_scaled_fibre_first_or_second A,
    eventually_maynardOptimizerFixedLogCost_absorbed A maynardLabelPolylogConstant
      (by
        dsimp only [maynardLabelPolylogConstant]
        positivity)
      120 400 (by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with T hscaled hlabelCost hlogT hT
  intro L X K mu N0 c alpha delta hX hL hXscale hLscale hmuLo hmuHi hc
    halphaLo halphaEndpoint hdelta S hS lam hgap hdiam color hcolor
  classical
  let d := routeTEndpointGlobalDeficit A T
  let nlabels : ℝ := Fintype.card (HeathBrownSelectionLabel L X 60)
  let B1 : ℝ := maynardHarmonicFactor K delta *
    T ^ (mu * (1 - alpha) - d / 200)
  let B2 : ℝ := maynardHarmonicFactor K delta *
    T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - d / 200)
  have hd : 0 < d := routeTEndpointGlobalDeficit_pos A (by linarith)
  have hT0 : 0 < T := by linarith
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
  have hlabelAbsorbedRaw := hlabelCost 1 0 (by norm_num)
    (by exact_mod_cast hT.le) (by omega : 0 ≤ maynardFixedPolylogExponentBound)
  have hlabelAbsorbed :
      maynardLabelPolylogConstant * (Real.log T) ^ 120 ≤ T ^ (d / 400) := by
    norm_num [d] at hlabelAbsorbedRaw ⊢
    exact hlabelAbsorbedRaw
  have hnlabels : nlabels ≤ T ^ (d / 400) := hlabelRaw.trans hlabelAbsorbed
  have hB10 : 0 ≤ B1 := by
    dsimp only [B1]
    exact mul_nonneg (maynardHarmonicFactor_pos K hdelta).le
      (Real.rpow_nonneg hT0.le _)
  have hB20 : 0 ≤ B2 := by
    dsimp only [B2]
    exact mul_nonneg (maynardHarmonicFactor_pos K hdelta).le
      (Real.rpow_nonneg hT0.le _)
  have hfibre : ∀ label : HeathBrownSelectionLabel L X 60,
      nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤ B1 ∨
      nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤ B2 := by
    intro label
    let Sf : Finset ℕ := S.filter fun r => color r = label
    by_cases hSf : Sf.Nonempty
    · have hSfS : Sf ⊆ S := Finset.filter_subset _ _
      have hSfRange : Sf ⊆ Finset.range K := hSfS.trans hS
      have hSfDiam : ∀ r ∈ Sf, ∀ s ∈ Sf, |lam s - lam r| ≤ T := by
        intro r hr s hs
        exact hdiam r (hSfS hr) s (hSfS hs)
      have hSfSelection : ∀ r ∈ Sf,
          IsMaynardWindowRelevantSelectedCell
            L X T mu N0 c (lam r) alpha label := by
        intro r hr
        have hrS := hSfS hr
        have hrcolor : color r = label := (Finset.mem_filter.mp hr).2
        simpa only [hrcolor] using hcolor r hrS
      simpa only [Sf, B1, B2] using
        hscaled hmuLo hmuHi hc halphaLo halphaEndpoint hdelta
          nlabels hnlabelsPos.le hnlabels label Sf hSf hSfRange lam hgap
          hSfDiam hSfSelection
    · have hzero : Sf.card = 0 :=
        Finset.card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hSf)
      left
      simpa only [Sf, hzero, Nat.cast_zero, mul_zero] using hB10
  have hcardCast : (S.card : ℝ) =
      ∑ label : HeathBrownSelectionLabel L X 60,
        (((S.filter fun r => color r = label).card : ℕ) : ℝ) := by
    exact_mod_cast card_eq_sum_color_fibres S color
  by_cases htargets : B1 ≤ B2
  · right
    have hsum : nlabels * (S.card : ℝ) ≤ nlabels * B2 := by
      rw [hcardCast, mul_sum]
      calc
        ∑ label : HeathBrownSelectionLabel L X 60,
            nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤
            ∑ _label : HeathBrownSelectionLabel L X 60, B2 :=
          Finset.sum_le_sum fun label _ => (hfibre label).elim
            (fun h => h.trans htargets) (fun h => h)
        _ = nlabels * B2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simpa only [B2] using (mul_le_mul_iff_right₀ hnlabelsPos).mp hsum
  · left
    have htargets' : B2 ≤ B1 := le_of_not_ge htargets
    have hsum : nlabels * (S.card : ℝ) ≤ nlabels * B1 := by
      rw [hcardCast, mul_sum]
      calc
        ∑ label : HeathBrownSelectionLabel L X 60,
            nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤
            ∑ _label : HeathBrownSelectionLabel L X 60, B1 :=
          Finset.sum_le_sum fun label _ => (hfibre label).elim
            (fun h => h) (fun h => h.trans htargets')
        _ = nlabels * B1 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simpa only [B1] using (mul_le_mul_iff_right₀ hnlabelsPos).mp hsum

end RHTower.Sieve
