import GaloisForLFunctions.RHTower.Sieve.LogWindowMultiplicative
import Mathlib.Algebra.Order.Chebyshev

/-!
# Tiling a long logarithmic window by short ones

A window of length `J·δ` is the disjoint union of `J` windows of length `δ`:

    ∑_{u < log n ≤ u + Jδ} a_n = ∑_{j < J} ∑_{u + jδ < log n ≤ u + (j+1)δ} a_n .

The identity is exact — each `n` falls in exactly one piece, the one indexed by `⌈(log n − u)/δ⌉ − 1`
— and with Cauchy–Schwarz it converts a mean square over long windows into `J` times a mean square
over short ones.  This is what reconciles the fixed `δ` of Gallagher's identity with a window length
prescribed in advance.
-/

namespace RHTower.Sieve

open Finset

/-- Membership in a shifted short window, in interval form. -/
theorem mem_logWindow_shift {δ u : ℝ} (n : ℕ) (j : ℕ) :
    u + j * δ ∈ logWindow δ n ↔
      ((j : ℝ) * δ < Real.log n - u ∧ Real.log n - u ≤ ((j : ℝ) + 1) * δ) := by
  rw [logWindow, Set.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by nlinarith [h1]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith [h2], by linarith⟩

/-- Exactly one short window contains a given point of a long window. -/
theorem sum_indicator_logWindow_shift {δ : ℝ} (hδ : 0 < δ) (J : ℕ) (n : ℕ) (u : ℝ) :
    (∑ j ∈ Finset.range J,
        Set.indicator (logWindow δ n) (fun _ => (1 : ℝ)) (u + j * δ))
      = Set.indicator (logWindow ((J : ℝ) * δ) n) (fun _ => (1 : ℝ)) u := by
  classical
  by_cases hmem : u ∈ logWindow ((J : ℝ) * δ) n
  · rw [Set.indicator_of_mem hmem]
    rw [logWindow, Set.mem_Ico] at hmem
    have hL0 : 0 < Real.log n - u := by linarith [hmem.2]
    have hLJ : Real.log n - u ≤ (J : ℝ) * δ := by linarith [hmem.1]
    have hdiv0 : 0 < (Real.log n - u) / δ := div_pos hL0 hδ
    set c : ℕ := ⌈(Real.log n - u) / δ⌉₊ with hc
    have hc1 : 1 ≤ c := by
      rw [hc, Nat.one_le_iff_ne_zero]
      intro h
      rw [Nat.ceil_eq_zero] at h
      linarith
    have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
    set j₀ : ℕ := c - 1 with hj₀
    have hj₀R : (j₀ : ℝ) = (c : ℝ) - 1 := by
      rw [hj₀, Nat.cast_sub hc1]
      norm_num
    have hup : Real.log n - u ≤ ((j₀ : ℝ) + 1) * δ := by
      rw [hj₀R]
      have h := Nat.le_ceil ((Real.log n - u) / δ)
      rw [← hc] at h
      rw [show (c : ℝ) - 1 + 1 = (c : ℝ) by ring, ← div_le_iff₀ hδ]
      exact h
    have hlow : (j₀ : ℝ) * δ < Real.log n - u := by
      rw [hj₀R]
      have h := Nat.ceil_lt_add_one hdiv0.le
      rw [← hc] at h
      rw [← lt_div_iff₀ hδ]
      linarith
    have hj₀mem : j₀ ∈ Finset.range J := by
      rw [Finset.mem_range, hj₀]
      have hcJ : c ≤ J := by
        rw [hc, Nat.ceil_le, div_le_iff₀ hδ]
        exact hLJ
      omega
    rw [Finset.sum_eq_single j₀]
    · rw [Set.indicator_of_mem ((mem_logWindow_shift n j₀).2 ⟨hlow, hup⟩)]
    · intro j _ hj
      refine Set.indicator_of_notMem (fun hcon => ?_) _
      rw [mem_logWindow_shift] at hcon
      obtain ⟨h1, h2⟩ := hcon
      rcases lt_or_gt_of_ne hj with hlt | hgt
      · have hle : (j : ℝ) + 1 ≤ (j₀ : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
        nlinarith [h2, hlow, hδ.le]
      · have hle : (j₀ : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
        nlinarith [h1, hup, hδ.le]
    · intro hcon
      exact absurd hj₀mem hcon
  · rw [Set.indicator_of_notMem hmem]
    refine Finset.sum_eq_zero fun j hj => ?_
    refine Set.indicator_of_notMem (fun hcon => ?_) _
    rw [mem_logWindow_shift] at hcon
    obtain ⟨h1, h2⟩ := hcon
    refine hmem ?_
    rw [logWindow, Set.mem_Ico]
    have hjJ : (j : ℝ) + 1 ≤ (J : ℝ) := by
      have := Finset.mem_range.1 hj
      exact_mod_cast Nat.succ_le_of_lt this
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    constructor
    · nlinarith [h2, hjJ, hδ.le]
    · nlinarith [h1, hj0, hδ.le]

/-- **A long logarithmic window is the disjoint union of `J` short ones.** -/
theorem logWindowSum_tiling (a : ℕ → ℂ) (s : Finset ℕ) {δ : ℝ} (hδ : 0 < δ) (J : ℕ) (u : ℝ) :
    logWindowSum a s ((J : ℝ) * δ) u
      = ∑ j ∈ Finset.range J, logWindowSum a s δ (u + j * δ) := by
  classical
  simp only [logWindowSum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_smul, sum_indicator_logWindow_shift hδ J n u]

/-- Cauchy–Schwarz over the pieces. -/
theorem normSq_sum_range_le (J : ℕ) (f : ℕ → ℂ) :
    ‖∑ j ∈ Finset.range J, f j‖ ^ 2 ≤ (J : ℝ) * ∑ j ∈ Finset.range J, ‖f j‖ ^ 2 := by
  have h1 : ‖∑ j ∈ Finset.range J, f j‖ ≤ ∑ j ∈ Finset.range J, ‖f j‖ := norm_sum_le _ _
  have h2 : (∑ j ∈ Finset.range J, ‖f j‖) ^ 2
      ≤ ((Finset.range J).card : ℝ) * ∑ j ∈ Finset.range J, ‖f j‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : ‖∑ j ∈ Finset.range J, f j‖ ^ 2 ≤ (∑ j ∈ Finset.range J, ‖f j‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [Finset.card_range] at h2
  linarith

/-- **The mean square over long windows, in terms of short ones.** -/
theorem normSq_logWindowSum_tiling_le (a : ℕ → ℂ) (s : Finset ℕ) {δ : ℝ} (hδ : 0 < δ) (J : ℕ)
    (u : ℝ) :
    ‖logWindowSum a s ((J : ℝ) * δ) u‖ ^ 2
      ≤ (J : ℝ) * ∑ j ∈ Finset.range J, ‖logWindowSum a s δ (u + j * δ)‖ ^ 2 := by
  rw [logWindowSum_tiling a s hδ J u]
  exact normSq_sum_range_le J _

end RHTower.Sieve
