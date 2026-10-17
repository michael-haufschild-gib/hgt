import GaloisForLFunctions.BiScaleUncertainty.FiniteIntegerTrainPeak
import Mathlib.Data.Fintype.Card

/-!
# An explicit diffuse train with distinct nonzero differences

Equal weights at integer sites `3^i` have mass equal to packet count and every
nonzero grouped lag coefficient equal to one. Thus their normalized peak vanishes.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

theorem ternary_pow_injective : Function.Injective (fun n : ℕ => (3 : ℤ) ^ n) := by
  intro a b hab
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · exact (ne_of_lt (pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 3) hlt)) hab
  · exact (ne_of_gt (pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 3) hgt)) hab

theorem ternary_difference_dominates {a b d : ℕ} (hab : a < b) (hdb : d < b) :
    (3 : ℤ) ^ d < 3 ^ b - 3 ^ a := by
  by_cases had : a ≤ d
  · have ha := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 3) had
    have hb := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 3) (show d + 1 ≤ b by omega)
    rw [pow_succ] at hb
    have hp : (0 : ℤ) < 3 ^ d := by positivity
    nlinarith only [ha, hb, hp]
  · have hd := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 3) (show d ≤ a by omega)
    have hb := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 3) (show a + 1 ≤ b by omega)
    rw [pow_succ] at hb
    have hp : (0 : ℤ) < 3 ^ a := by positivity
    nlinarith only [hd, hb, hp]

theorem ternary_positive_difference_injective {a b c d : ℕ} (hab : a < b) (hcd : c < d)
    (he : (3 : ℤ) ^ b - 3 ^ a = 3 ^ d - 3 ^ c) : a = c ∧ b = d := by
  have hbd : b = d := by
    rcases lt_trichotomy b d with hlt | heq | hgt
    · have hd := ternary_difference_dominates hcd hlt
      have hp : (0 : ℤ) < 3 ^ a := by positivity
      omega
    · exact heq
    · have hb := ternary_difference_dominates hab hgt
      have hp : (0 : ℤ) < 3 ^ c := by positivity
      omega
  subst d
  have hpow : (3 : ℤ) ^ a = 3 ^ c := by linarith only [he]
  exact ⟨ternary_pow_injective hpow, rfl⟩

theorem ternary_nonzero_difference_injective {a b c d : ℕ} (hab : a ≠ b)
    (he : (3 : ℤ) ^ b - 3 ^ a = 3 ^ d - 3 ^ c) : a = c ∧ b = d := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have hpos : (3 : ℤ) ^ a < 3 ^ b := pow_lt_pow_right₀ (by norm_num) hlt
    have hcd : c < d := by
      by_contra hn
      have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 3) (show d ≤ c by omega)
      omega
    exact ternary_positive_difference_injective hlt hcd he
  · have hpos : (3 : ℤ) ^ b < 3 ^ a := pow_lt_pow_right₀ (by norm_num) hgt
    have hdc : d < c := by
      by_contra hn
      have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 3) (show c ≤ d by omega)
      omega
    have hh := ternary_positive_difference_injective hgt hdc (show (3 : ℤ) ^ a - 3 ^ b = 3 ^ c - 3 ^ d by omega)
    exact ⟨hh.2, hh.1⟩

def ternaryPacketTrain (n : ℕ) : IntegerPacketTrain where
  last := n + 1
  coefficient := fun _ => 1
  site := fun i => (3 : ℤ) ^ i.val
  site_injective := by
    intro i j hij
    exact Fin.ext (ternary_pow_injective hij)
  coefficient_nonzero := ⟨0, one_ne_zero⟩

theorem ternaryPacketTrain_mass (n : ℕ) : (ternaryPacketTrain n).mass = (n : ℝ) + 2 := by
  change (∑ _i : Fin ((n + 1) + 1), (1 : ℝ) ^ 2) = (n : ℝ) + 2
  simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
  ring

theorem ternaryPacketTrain_difference_unique (n : ℕ)
    {i j k l : Fin ((n + 1) + 1)}
    (hij : (ternaryPacketTrain n).site j - (ternaryPacketTrain n).site i ≠ 0)
    (he : (ternaryPacketTrain n).site j - (ternaryPacketTrain n).site i =
      (ternaryPacketTrain n).site l - (ternaryPacketTrain n).site k) : i = k ∧ j = l := by
  have hv : i.val ≠ j.val := by
    intro hv
    apply hij
    simp only [ternaryPacketTrain, hv, sub_self]
  have h := ternary_nonzero_difference_injective hv he
  exact ⟨Fin.ext h.1, Fin.ext h.2⟩

/-- Each nonzero packet is produced by exactly one ordered source pair. -/
theorem ternaryPacketTrain_lagCoefficient (n : ℕ) {r : ℤ}
    (hr : r ∈ (ternaryPacketTrain n).lags) (hr0 : r ≠ 0) :
    (ternaryPacketTrain n).lagCoefficient r = 1 := by
  classical
  let d := ternaryPacketTrain n
  obtain ⟨⟨i, j⟩, _, hij⟩ := Finset.mem_image.mp hr
  change d.site j - d.site i = r at hij
  have hne : d.site j - d.site i ≠ 0 := by simpa only [hij] using hr0
  change d.lagCoefficient r = 1
  unfold IntegerPacketTrain.lagCoefficient
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · rw [if_pos hij]
      change (1 : ℝ) * 1 = 1
      norm_num
    · intro l _ hlj
      have hn : d.site l - d.site i ≠ r := by
        intro he
        have hh := ternaryPacketTrain_difference_unique n hne (hij.trans he.symm)
        exact hlj hh.2.symm
      simp only [if_neg hn]
    · simp
  · intro k _ hki
    apply Finset.sum_eq_zero
    intro l _
    have hn : d.site l - d.site k ≠ r := by
      intro he
      have hh := ternaryPacketTrain_difference_unique n hne (hij.trans he.symm)
      exact hki hh.1.symm
    simp only [if_neg hn]
  · simp

theorem ternaryPacketTrain_two_mem_lags (n : ℕ) : 2 ∈ (ternaryPacketTrain n).lags := by
  let i : Fin ((n + 1) + 1) := ⟨0, by omega⟩
  let j : Fin ((n + 1) + 1) := ⟨1, by omega⟩
  have h := (ternaryPacketTrain n).difference_mem_lags i j
  simpa only [ternaryPacketTrain, i, j, pow_zero, pow_one, show (3 : ℤ) - 1 = 2 by norm_num] using h

theorem ternaryPacketTrain_rawPeak (n : ℕ) : (ternaryPacketTrain n).rawPeak = 1 := by
  classical
  let d := ternaryPacketTrain n
  apply le_antisymm
  · apply d.peakValues.max'_le
    intro y hy
    rcases Finset.mem_insert.mp hy with hz | hy
    · rw [hz]
      norm_num
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hk0, hk⟩ := Finset.mem_erase.mp hk
      rw [ternaryPacketTrain_lagCoefficient n hk hk0, abs_one]
  · have h := d.lagCoefficient_le_rawPeak (ternaryPacketTrain_two_mem_lags n) (by norm_num : (2 : ℤ) ≠ 0)
    change |(ternaryPacketTrain n).lagCoefficient 2| ≤ (ternaryPacketTrain n).rawPeak at h
    simpa only [ternaryPacketTrain_lagCoefficient n (ternaryPacketTrain_two_mem_lags n)
      (by norm_num : (2 : ℤ) ≠ 0), abs_one] using h

theorem ternaryPacketTrain_peak (n : ℕ) : (ternaryPacketTrain n).peak = 1 / ((n : ℝ) + 2) := by
  rw [IntegerPacketTrain.peak, ternaryPacketTrain_rawPeak, ternaryPacketTrain_mass]

theorem ternaryPacketTrain_mass_fraction (n : ℕ) (i : Fin ((n + 1) + 1)) :
    (ternaryPacketTrain n).coefficient i ^ 2 / (ternaryPacketTrain n).mass = 1 / ((n : ℝ) + 2) := by
  rw [ternaryPacketTrain_mass]
  simp only [ternaryPacketTrain, one_pow]

end
end GaloisForLFunctions.BiScaleUncertainty
