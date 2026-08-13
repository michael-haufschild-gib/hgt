import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellMiddleFibreCount
import GaloisForLFunctions.RHTower.Sieve.MaynardLabelAbsorption

/-!
# Global middle-strip count from selected-cell fibres

The complete finite label space is summed without choosing a receiver fibre-by-fibre.  A fixed
fraction of the middle deficit absorbs label entropy, then the larger global receiver controls all
fibres and the positive label count cancels.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- **Global middle-strip Route-T dichotomy.**  Literal selected-cell coloring, including the
unique overweight cell, satisfies one receiver with a residual `d/4000` power margin. -/
theorem eventually_card_le_maynard_first_or_second_of_selected_cell_coloring_middle :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      1 ≤ X → 1 ≤ L →
      (X : ℝ) ≤ T ^ mu → (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 / 2 ≤ c → 19 / 25 ≤ alpha → alpha ≤ 997 / 1000 →
      0 < delta →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      ∀ (color : ℕ → HeathBrownSelectionLabel L X 60),
      (∀ r ∈ S, IsMaynardWindowRelevantSelectedCell
        L X T mu N0 c (lam r) alpha (color r)) →
      (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
          T ^ (mu * (1 - alpha) - maynardLongGlobalAmplitudeDeficit / 4000) ∨
        (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
          T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) -
            maynardLongGlobalAmplitudeDeficit / 4000) := by
  filter_upwards [
    eventually_maynardWindowRelevantSelectedCell_middle_fibre_first_or_second,
    eventually_maynardMiddleFixedLogCost_absorbed maynardLabelPolylogConstant
      (by
        dsimp only [maynardLabelPolylogConstant]
        positivity)
      120 4000 (by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with T hfibre hlabelCost hlogT hT
  intro L X K mu N0 c alpha delta hX hL hXscale hLscale hmuLo hmuHi hc
    halphaLo halphaHi hdelta S hS lam hgap hband color hcolor
  classical
  let d : ℝ := maynardLongGlobalAmplitudeDeficit
  let nlabels : ℝ := Fintype.card (HeathBrownSelectionLabel L X 60)
  let B1 : ℝ := maynardHarmonicFactor K delta *
    T ^ (mu * (1 - alpha) - d / 4000)
  let B2 : ℝ := maynardHarmonicFactor K delta *
    T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - d / 4000)
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
  have hlabelAbsorbedRaw := hlabelCost 1 0 (by norm_num)
    (by exact_mod_cast one_le_pow₀ (n := 90) hT.le)
    (by omega : 0 ≤ maynardMontgomeryFixedPolylogExponentBound)
  have hlabelAbsorbed :
      maynardLabelPolylogConstant * (Real.log T) ^ 120 ≤ T ^ (d / 4000) := by
    norm_num [d] at hlabelAbsorbedRaw ⊢
    exact hlabelAbsorbedRaw
  have hnlabels : nlabels ≤ T ^ (d / 4000) := hlabelRaw.trans hlabelAbsorbed
  have hB10 : 0 ≤ B1 := by
    dsimp only [B1]
    exact mul_nonneg (maynardHarmonicFactor_pos K hdelta).le
      (Real.rpow_nonneg hT0.le _)
  have hB20 : 0 ≤ B2 := by
    dsimp only [B2]
    exact mul_nonneg (maynardHarmonicFactor_pos K hdelta).le
      (Real.rpow_nonneg hT0.le _)
  have hpowMerge1 :
      T ^ (d / 4000) *
          (maynardHarmonicFactor K delta *
            T ^ (mu * (1 - alpha) - d / 2000)) = B1 := by
    dsimp only [B1]
    rw [mul_left_comm, ← Real.rpow_add hT0]
    congr 1
    ring
  have hpowMerge2 :
      T ^ (d / 4000) *
          (maynardHarmonicFactor K delta *
            T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - d / 2000)) =
        B2 := by
    dsimp only [B2]
    rw [mul_left_comm, ← Real.rpow_add hT0]
    congr 1
    ring
  have hfibres : ∀ label : HeathBrownSelectionLabel L X 60,
      nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤ B1 ∨
      nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤ B2 := by
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
      rcases hfibre hmuLo hmuHi hc halphaLo halphaHi hdelta label
          Sf hSf hSfRange lam hgap hSfBand hSfSelection with hfirst | hsecond
      · left
        calc
          nlabels * (Sf.card : ℝ) ≤ T ^ (d / 4000) *
              (maynardHarmonicFactor K delta *
                T ^ (mu * (1 - alpha) - d / 2000)) :=
            mul_le_mul hnlabels hfirst (Nat.cast_nonneg _)
              (Real.rpow_nonneg hT0.le _)
          _ = B1 := hpowMerge1
      · right
        calc
          nlabels * (Sf.card : ℝ) ≤ T ^ (d / 4000) *
              (maynardHarmonicFactor K delta *
                T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - d / 2000)) :=
            mul_le_mul hnlabels hsecond (Nat.cast_nonneg _)
              (Real.rpow_nonneg hT0.le _)
          _ = B2 := hpowMerge2
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
          Finset.sum_le_sum fun label _ => (hfibres label).elim
            (fun h => h.trans htargets) (fun h => h)
        _ = nlabels * B2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simpa only [B2, d] using (mul_le_mul_iff_right₀ hnlabelsPos).mp hsum
  · left
    have htargets' : B2 ≤ B1 := le_of_not_ge htargets
    have hsum : nlabels * (S.card : ℝ) ≤ nlabels * B1 := by
      rw [hcardCast, mul_sum]
      calc
        ∑ label : HeathBrownSelectionLabel L X 60,
            nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤
            ∑ _label : HeathBrownSelectionLabel L X 60, B1 :=
          Finset.sum_le_sum fun label _ => (hfibres label).elim
            (fun h => h) (fun h => h.trans htargets')
        _ = nlabels * B1 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simpa only [B1, d] using (mul_le_mul_iff_right₀ hnlabelsPos).mp hsum

end RHTower.Sieve
