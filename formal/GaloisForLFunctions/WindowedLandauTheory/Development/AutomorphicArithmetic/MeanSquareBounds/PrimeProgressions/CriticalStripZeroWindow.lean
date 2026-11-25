import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.PrincipalRightHalfZeroWindow
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.PrimitiveZeroReflection

/-! Uniform zero multiplicities across the critical strip in a unit-height window. -/

open Complex Finset
open WindowedLandauTheory.ZeroFreeDirichlet

noncomputable section

namespace QH.PrimeProgressions

private theorem ls_shift_le {N : ℕ} [NeZero N] {t u : ℝ} (h : |u| ≤ |t| + 1) :
    Real.log ((N : ℝ) * (|u| + 2)) ≤ 2 * Real.log ((N : ℝ) * (|t| + 2)) :=
  (Real.log_le_log (mul_pos (Nat.cast_pos.mpr (NeZero.pos N)) (by positivity))
    (mul_le_mul_of_nonneg_left (by linarith only [h])
    (Nat.cast_nonneg _))).trans (log_height_shift N t)

private theorem right_zero_window :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) (Z : Finset ℂ),
      (∀ ρ ∈ Z, χ.LFunction ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1) →
      (∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤ C * Real.log ((N : ℝ) * (|t| + 2)) := by
  obtain ⟨P, hP, hp⟩ := principal_half_height_right_zero_count
  obtain ⟨Q, hQ, hq⟩ := nonprincipal_half_height_right_zero_count
  let C := max P Q
  have hC : 0 < C := hP.trans_le (le_max_left _ _)
  have half (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) (Z : Finset ℂ)
      (hZ : ∀ ρ ∈ Z, χ.LFunction ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 / 2) :
      (∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤ C * Real.log ((N : ℝ) * (|t| + 2)) := by
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
    have hlog : 0 ≤ Real.log ((N : ℝ) * (|t| + 2)) := by
      apply Real.log_nonneg
      exact le_trans (by linarith only [abs_nonneg t]) (le_mul_of_one_le_left (by positivity) hN)
    rcases eq_or_ne χ 1 with rfl | hχ
    · exact (hp N Z t (fun ρ hρ => (hZ ρ hρ).2)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog)
    · exact (hq N χ hχ Z t (fun ρ hρ => ⟨(hZ ρ hρ).1, (hZ ρ hρ).2.1, (hZ ρ hρ).2.2.2⟩)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hlog)
  refine ⟨4 * C, by positivity, ?_⟩
  intro N _ χ t Z hZ
  classical
  let a : ℝ := t - 1 / 2
  let b : ℝ := t + 1 / 2
  have ha := half N χ a (Z.filter fun ρ => ρ.im ≤ t) (by
    intro ρ hρ
    obtain ⟨hρ, hle⟩ := mem_filter.mp hρ
    obtain ⟨hz, h₀, h₁, ht⟩ := hZ ρ hρ
    refine ⟨hz, h₀, h₁, abs_le.mpr ⟨?_, ?_⟩⟩ <;> dsimp only [a] <;>
      linarith only [hle, (abs_le.mp ht).1])
  have hb := half N χ b (Z.filter fun ρ => ¬ ρ.im ≤ t) (by
    intro ρ hρ
    obtain ⟨hρ, hgt⟩ := mem_filter.mp hρ
    obtain ⟨hz, h₀, h₁, ht⟩ := hZ ρ hρ
    refine ⟨hz, h₀, h₁, abs_le.mpr ⟨?_, ?_⟩⟩ <;> dsimp only [b] <;>
      linarith only [lt_of_not_ge hgt, (abs_le.mp ht).2])
  have ha' : |a| ≤ |t| + 1 := by
    dsimp only [a]
    have ht := abs_add_le t (-(1 / 2 : ℝ))
    rw [← sub_eq_add_neg, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at ht
    linarith only [ht]
  have hb' : |b| ≤ |t| + 1 := by
    dsimp only [b]
    exact (abs_add_le _ _).trans (by norm_num)
  rw [← sum_filter_add_sum_filter_not Z (fun ρ => ρ.im ≤ t)]
  have e := add_le_add (ha.trans (mul_le_mul_of_nonneg_left (ls_shift_le (N := N) ha') hC.le))
    (hb.trans (mul_le_mul_of_nonneg_left (ls_shift_le (N := N) hb') hC.le))
  refine e.trans_eq ?_
  ring

/-- The analytic multiplicities in the critical strip sum to at most a uniform logarithmic bound. -/
theorem primitive_critical_strip_zero_window :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ (t : ℝ) (Z : Finset ℂ),
        (∀ ρ ∈ Z, χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1) →
        (∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤ C * Real.log ((N : ℝ) * (|t| + 2)) := by
  obtain ⟨C, hC, H⟩ := right_zero_window
  refine ⟨2 * C, by positivity, ?_⟩
  intro N _ χ hχ t Z hZ
  classical
  let Zright := Z.filter fun ρ => 1 / 2 ≤ ρ.re
  let Zleft := Z.filter fun ρ => ¬ 1 / 2 ≤ ρ.re
  have hright := H N χ t Zright (by
    intro ρ hρ
    obtain ⟨hρ, h₀⟩ := mem_filter.mp hρ
    exact ⟨(hZ ρ hρ).1, h₀, (hZ ρ hρ).2.2⟩)
  let e : ℂ ↪ ℂ := ⟨fun ρ => 1 - ρ, fun a b h => by
    change (1 : ℂ) - a = 1 - b at h
    linear_combination -h⟩
  have hleft := H N χ⁻¹ (-t) (Zleft.map e) (by
    intro ρ hρ
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hρ
    obtain ⟨ha', h₁⟩ := mem_filter.mp ha
    obtain ⟨hz, h₀, h₁', ht⟩ := hZ a ha'
    have r₀ : 0 < (e a).re := by change 0 < (1 - a).re; simp only [sub_re, one_re, sub_pos]; exact h₁'
    have r₁ : (e a).re < 1 := by change (1 - a).re < 1; rw [sub_re, one_re]; linarith only [h₀]
    have hR : 1 - e a = a := by change 1 - (1 - a) = a; ring
    refine ⟨(LFunction_one_sub_eq_zero_iff hχ r₀ r₁).1 (by rwa [hR]), ?_, r₁, ?_⟩
    · change 1 / 2 ≤ (1 - a).re
      rw [sub_re, one_re]
      linarith only [lt_of_not_ge h₁]
    · change |(1 - a).im - -t| ≤ 1
      simpa only [sub_im, one_im, zero_sub, neg_sub_neg, abs_sub_comm] using ht)
  rw [sum_map, abs_neg] at hleft
  have hc : (∑ ρ ∈ Zleft, (analyticOrderNatAt χ.LFunction ρ : ℝ)) =
      ∑ a ∈ Zleft, (analyticOrderNatAt (χ⁻¹).LFunction (e a) : ℝ) := by
    refine sum_congr rfl fun a ha => ?_
    have h := (hZ a (mem_filter.mp ha).1).2.1
    have h' := (hZ a (mem_filter.mp ha).1).2.2.1
    have r₀ : 0 < (e a).re := by change 0 < (1 - a).re; simp only [sub_re, one_re, sub_pos]; exact h'
    have r₁ : (e a).re < 1 := by change (1 - a).re < 1; rw [sub_re, one_re]; linarith only [h]
    have hR : 1 - e a = a := by change 1 - (1 - a) = a; ring
    have horder := analyticOrderNatAt_LFunction_one_sub hχ r₀ r₁
    rw [hR] at horder
    exact_mod_cast horder
  rw [← sum_filter_add_sum_filter_not Z (fun ρ => 1 / 2 ≤ ρ.re)]
  change _ + ∑ ρ ∈ Zleft, _ ≤ _
  rw [hc]
  exact (add_le_add hright hleft).trans_eq (by ring)

end QH.PrimeProgressions
