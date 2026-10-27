import GaloisForLFunctions.BiScaleUncertainty.DyadicMantissaVariance

/-!
# Explicit high and low counts in the last dyadic tent level

Half of the last level is at least one quarter, and a quarter is at most
one eighth. The same tent supplies a nonconstant doubling-null vector on
every stated dyadic window.
-/

noncomputable section
open Finset
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
set_option autoImplicit false

private theorem last_level_formula (h n : ℕ) (hlo : 8 * 2 ^ h ≤ n)
    (hhi : n ≤ 16 * 2 ^ h) :
    dyadicMantissaTent n =
      min ((n : ℝ) - 8 * (2 : ℝ) ^ h) (16 * (2 : ℝ) ^ h - (n : ℝ)) /
        (8 * (2 : ℝ) ^ h) := by
  have h8 : (2 : ℕ) ^ (h + 3) = 8 * 2 ^ h := by rw [pow_add]; norm_num; ring
  have h16 : (2 : ℕ) ^ (h + 3 + 1) = 16 * 2 ^ h := by rw [pow_add, pow_add]; norm_num; ring
  have h8R : (2 : ℝ) ^ (h + 3) = 8 * (2 : ℝ) ^ h := by rw [pow_add]; norm_num; ring
  have h16R : (2 : ℝ) ^ (h + 3 + 1) = 16 * (2 : ℝ) ^ h := by
    rw [pow_add, pow_add]; norm_num; ring
  rw [dyadicMantissaTent_eq_level (h + 3) n (by rwa [h8]) (by rwa [h16]), h8R, h16R]

/-- The middle half of the final level has tent value at least one quarter. -/
theorem dyadicMantissaTent_high_block (h n : ℕ)
    (hn : n ∈ Ico (10 * 2 ^ h) (14 * 2 ^ h)) :
    (1 : ℝ) / 4 ≤ dyadicMantissaTent n := by
  have hn' := mem_Ico.mp hn
  have hr : 0 < (2 : ℝ) ^ h := by positivity
  have hlo : 10 * (2 : ℝ) ^ h ≤ (n : ℝ) := by exact_mod_cast hn'.1
  have hhi : (n : ℝ) < 14 * (2 : ℝ) ^ h := by exact_mod_cast hn'.2
  rw [last_level_formula h n (by omega) (by omega)]
  apply (le_div_iff₀ (mul_pos (by norm_num) hr)).mpr
  apply le_min <;> linarith only [hlo, hhi]

/-- Both outer eighths of the final level have tent value at most one eighth. -/
theorem dyadicMantissaTent_low_blocks (h n : ℕ)
    (hn : n ∈ Ico (8 * 2 ^ h) (9 * 2 ^ h) ∪ Ico (15 * 2 ^ h) (16 * 2 ^ h)) :
    dyadicMantissaTent n ≤ (1 : ℝ) / 8 := by
  have hr : 0 < (2 : ℝ) ^ h := by positivity
  rcases mem_union.mp hn with hn | hn
  · have hn' := mem_Ico.mp hn
    have hhi : (n : ℝ) < 9 * (2 : ℝ) ^ h := by exact_mod_cast hn'.2
    rw [last_level_formula h n hn'.1 (by omega)]
    apply (div_le_iff₀ (mul_pos (by norm_num) hr)).mpr
    exact (min_le_left _ _).trans (by linarith only [hhi])
  · have hn' := mem_Ico.mp hn
    have hlo : 15 * (2 : ℝ) ^ h ≤ (n : ℝ) := by exact_mod_cast hn'.1
    rw [last_level_formula h n (by omega) hn'.2.le]
    apply (div_le_iff₀ (mul_pos (by norm_num) hr)).mpr
    exact (min_le_right _ _).trans (by linarith only [hlo])

/-- At least half of the last level is high, with the exact dyadic count. -/
theorem dyadicMantissaTent_high_count (h : ℕ) :
    4 * 2 ^ h ≤ ((Ico (8 * 2 ^ h) (16 * 2 ^ h)).filter
      (fun n => (1 : ℝ) / 4 ≤ dyadicMantissaTent n)).card := by
  classical
  have hsub : Ico (10 * 2 ^ h) (14 * 2 ^ h) ⊆
      (Ico (8 * 2 ^ h) (16 * 2 ^ h)).filter
        (fun n => (1 : ℝ) / 4 ≤ dyadicMantissaTent n) := by
    intro n hn
    have hn' := mem_Ico.mp hn
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, dyadicMantissaTent_high_block h n hn⟩
  have hcount : (Ico (10 * 2 ^ h) (14 * 2 ^ h)).card = 4 * 2 ^ h := by
    rw [Nat.card_Ico]
    omega
  rw [← hcount]
  exact card_le_card hsub

/-- At least a quarter of the last level is low; the two counted blocks are disjoint. -/
theorem dyadicMantissaTent_low_count (h : ℕ) :
    2 * 2 ^ h ≤ ((Ico (8 * 2 ^ h) (16 * 2 ^ h)).filter
      (fun n => dyadicMantissaTent n ≤ (1 : ℝ) / 8)).card := by
  classical
  have hd : Disjoint (Ico (8 * 2 ^ h) (9 * 2 ^ h)) (Ico (15 * 2 ^ h) (16 * 2 ^ h)) := by
    apply disjoint_left.mpr
    intro n hn hm
    have hn' := mem_Ico.mp hn
    have hm' := mem_Ico.mp hm
    omega
  have hsub : Ico (8 * 2 ^ h) (9 * 2 ^ h) ∪ Ico (15 * 2 ^ h) (16 * 2 ^ h) ⊆
      (Ico (8 * 2 ^ h) (16 * 2 ^ h)).filter
        (fun n => dyadicMantissaTent n ≤ (1 : ℝ) / 8) := by
    intro n hn
    refine mem_filter.mpr ⟨?_, dyadicMantissaTent_low_blocks h n hn⟩
    rcases mem_union.mp hn with hn | hn
    · have hn' := mem_Ico.mp hn
      exact mem_Ico.mpr ⟨hn'.1, by omega⟩
    · have hn' := mem_Ico.mp hn
      exact mem_Ico.mpr ⟨by omega, hn'.2⟩
  have hcount : (Ico (8 * 2 ^ h) (9 * 2 ^ h) ∪ Ico (15 * 2 ^ h) (16 * 2 ^ h)).card =
      2 * 2 ^ h := by
    rw [card_union_of_disjoint hd, Nat.card_Ico, Nat.card_Ico]
    omega
  rw [← hcount]
  exact card_le_card hsub

/-- Both counts have the exact fractions of the last-level size used in the variance argument. -/
theorem dyadicMantissaTent_last_level_counts (h : ℕ) :
    let q := 2 ^ (h + 3)
    q / 2 ≤ ((Ico q (2 * q)).filter (fun n => (1 : ℝ) / 4 ≤ dyadicMantissaTent n)).card ∧
      q / 4 ≤ ((Ico q (2 * q)).filter (fun n => dyadicMantissaTent n ≤ (1 : ℝ) / 8)).card := by
  have hq : (2 : ℕ) ^ (h + 3) = 8 * 2 ^ h := by rw [pow_add]; norm_num; ring
  dsimp only
  rw [hq, show 2 * (8 * 2 ^ h) = 16 * 2 ^ h by omega,
    show 8 * 2 ^ h / 2 = 4 * 2 ^ h by omega,
    show 8 * 2 ^ h / 4 = 2 * 2 ^ h by omega]
  exact ⟨dyadicMantissaTent_high_count h, dyadicMantissaTent_low_count h⟩

/-- No finite constant controls distance to constants by doubling energy alone. -/
theorem not_doubling_only_window_coercivity (h : ℕ) (C : ℝ) :
    ¬ (∀ f : ℕ → ℝ, ∃ c : ℝ,
      (∑ n ∈ Icc 1 (2 ^ (h + 4) - 1), (f n - c) ^ 2) ≤
        C * multiplicativeScaleEnergy 2 (2 ^ (h + 4) - 1) f) := by
  intro hC
  obtain ⟨c, hc⟩ := hC dyadicMantissaTent
  rw [multiplicativeScaleEnergy_dyadicMantissaTent, mul_zero] at hc
  have hv := dyadicMantissaTent_variance_lower h c
  have hpow : (2 : ℕ) ^ (h + 4) = 16 * 2 ^ h := by rw [pow_add]; norm_num; ring
  have hr : 0 < (2 : ℕ) ^ h := by positivity
  have hN : (0 : ℝ) < ((2 ^ (h + 4) - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < (2 : ℕ) ^ (h + 4) - 1 by rw [hpow]; omega)
  linarith only [hc, hv, hN]

end GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
