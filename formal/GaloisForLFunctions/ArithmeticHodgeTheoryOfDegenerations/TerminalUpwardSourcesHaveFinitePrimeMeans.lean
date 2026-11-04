import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalUpwardModelsHaveFinitePrimeSources
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalUpwardRowReplacementDisappears
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWindowErrorChannelsDisappear

/-!
# Actual terminal upward sources have finite prime means

The finite prime mean of the polar model survives the actual-row
replacement. Every fixed nonpolar model and its replacement error
vanish. These statements hold throughout every positive critical ratio.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory

/-- The actual polar upward row retains its finite prime-power source. -/
theorem tendsto_terminal_upwardModeRow_one
    {φ F : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {B LF δ : ℝ} (hδ : 0 < δ) (hF : ∀ x, |F x| ≤ B)
    (hzero : ∀ x, x ≤ δ → F x = 0) (hLF : 0 ≤ LF)
    (hFL : ∀ x y, |F x - F y| ≤ LF * |x - y|)
    {K : ℕ} (hK : 1 / δ ≤ K) {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (hcTop : Tendsto c atTop atTop)
    (hc4 : Tendsto (fun N : ℕ => c N ^ 4 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n * upwardModeRow φ (c N) N 1 n) / c N)
      atTop (𝓝 (((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) * finitePrimeTerminalMean F K)) := by
  have herror := tendsto_terminal_upward_row_sub_model hφ hsupp hM hδ hF hzero 1 hc hc4
  have hmodel := tendsto_terminal_upwardModel_one hφ hsupp hM hδ hF hzero hLF hFL hK hc hcTop
  simpa only [mul_sub, sum_sub_distrib, sub_div, sub_add_cancel, zero_add] using herror.add hmodel

/-- The actual nonpolar upward row vanishes against every bounded terminal receiver. -/
theorem tendsto_terminal_upwardModeRow_nonpolar
    {φ F : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {B δ : ℝ} (hδ : 0 < δ) (hF : ∀ x, |F x| ≤ B)
    (hzero : ∀ x, x ≤ δ → F x = 0)
    {m : ℕ} (hm : 2 ≤ m) {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (hcTop : Tendsto c atTop atTop)
    (hc4 : Tendsto (fun N : ℕ => c N ^ 4 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n * upwardModeRow φ (c N) N m n) / c N)
      atTop (𝓝 0) := by
  have herror := tendsto_terminal_upward_row_sub_model hφ hsupp hM hδ hF hzero m hc hc4
  have hmodel := tendsto_terminal_upwardModel_nonpolar hφ hsupp hM hδ hF hzero hm hc hcTop
  simpa only [mul_sub, sum_sub_distrib, sub_div, sub_add_cancel, zero_add] using herror.add hmodel

/-- The complete terminal upward mean is polar at every positive critical ratio. -/
theorem tendsto_terminal_upwardModeRow_critical
    {φ F : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {B LF δ : ℝ} (hδ : 0 < δ) (hF : ∀ x, |F x| ≤ B)
    (hzero : ∀ x, x ≤ δ → F x = 0) (hLF : 0 ≤ LF)
    (hFL : ∀ x y, |F x - F y| ≤ LF * |x - y|)
    {K m : ℕ} (hK : 1 / δ ≤ K) (hm : 1 ≤ m)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n * upwardModeRow φ (c N) N m n) / c N)
      atTop (𝓝 (if m = 1 then
        ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) * finitePrimeTerminalMean F K else 0)) := by
  have hcTop := (criticalCurve_facts hc hR hcrit).1
  have hc4 := criticalCurve_pow_log_div_natCast hc hR hcrit 4 0
  simp only [pow_zero, mul_one] at hc4
  by_cases hm1 : m = 1
  · subst m
    rw [if_pos rfl]
    exact tendsto_terminal_upwardModeRow_one hφ hsupp hM hδ hF hzero hLF hFL hK hc hcTop hc4
  · rw [if_neg hm1]
    exact tendsto_terminal_upwardModeRow_nonpolar hφ hsupp hM hδ hF hzero (by omega) hc hcTop hc4

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_upwardModeRow_one
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_upwardModeRow_nonpolar
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_upwardModeRow_critical
