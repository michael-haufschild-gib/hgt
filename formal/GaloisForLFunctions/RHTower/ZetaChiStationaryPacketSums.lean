import GaloisForLFunctions.RHTower.ZetaChiIntegerStationaryPackets

open Complex
open scoped BigOperators
noncomputable section
namespace RHTower

/-- A common chi orientation controls the signed aggregate of every finite
integer-frequency packet, retaining its actual complex coefficients. -/
theorem exists_zetaChi_stationary_packet_sum_bound :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ S : Finset ℕ, ∀ c : ℕ → ℂ,
      (∀ n ∈ S, 0 < n) → ∀ t : ℝ, 4 ≤ t →
      ‖(∑ n ∈ S, c n * (zetaChi (linePt t) *
        Complex.exp (((t * Real.log n : ℝ) : ℂ) * I))) - κ * ∑ n ∈ S, c n‖ ≤
      ∑ n ∈ S, ‖c n‖ * (26 / t +
        (t - 2 * Real.pi * n) ^ 2 / (2 * Real.pi * n)) := by
  obtain ⟨κ, hκ, h⟩ := exists_zetaChi_integer_stationary_alignment
  refine ⟨κ, hκ, ?_⟩
  intro S c hS t ht
  have he : (∑ n ∈ S, c n * (zetaChi (linePt t) *
        Complex.exp (((t * Real.log n : ℝ) : ℂ) * I))) - κ * ∑ n ∈ S, c n =
      ∑ n ∈ S, c n * (zetaChi (linePt t) *
        Complex.exp (((t * Real.log n : ℝ) : ℂ) * I) - κ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (h n (hS n hn) t ht) (norm_nonneg _)

private theorem unit_rotated_real_lower {κ z : ℂ} {A E : ℝ}
    (hκ : ‖κ‖ = 1) (h : ‖z - κ * (A : ℂ)‖ ≤ E) :
    A - E ≤ ((starRingEnd ℂ) κ * z).re := by
  have hu : (starRingEnd ℂ) κ * κ = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hκ]
    norm_num
  have he : (starRingEnd ℂ) κ * (z - κ * (A : ℂ)) =
      (starRingEnd ℂ) κ * z - (A : ℂ) := by
    rw [mul_sub, ← mul_assoc, hu, one_mul]
  have hb : ‖(starRingEnd ℂ) κ * z - (A : ℂ)‖ ≤ E := by
    rw [← he, norm_mul, Complex.norm_conj, hκ, one_mul]
    exact h
  have hr := (neg_le_abs (((starRingEnd ℂ) κ * z - (A : ℂ)).re)).trans
    ((Complex.abs_re_le_norm _).trans hb)
  simp only [Complex.sub_re, Complex.ofReal_re] at hr
  linarith

/-- Nonnegative coefficients in the actual stationary window have a positive
physical sum in one fixed direction, uniformly over every finite packet. -/
theorem exists_zetaChi_stationary_positive_packet :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ S : Finset ℕ, ∀ c : ℕ → ℝ,
      (∀ n ∈ S, 0 < n) → (∀ n ∈ S, 0 ≤ c n) →
      ∀ t : ℝ, 104 ≤ t →
      (∀ n ∈ S, (t - 2 * Real.pi * n) ^ 2 ≤ (2 * Real.pi * n) / 4) →
      (∑ n ∈ S, c n) / 2 ≤ ((starRingEnd ℂ) κ *
        ∑ n ∈ S, (c n : ℂ) * (zetaChi (linePt t) *
          Complex.exp (((t * Real.log n : ℝ) : ℂ) * I))).re := by
  obtain ⟨κ, hκ, h⟩ := exists_zetaChi_stationary_packet_sum_bound
  refine ⟨κ, hκ, ?_⟩
  intro S c hS hc t ht hd
  have ht0 : 0 < t := by linarith
  have hb := h S (fun n => (c n : ℂ)) hS t (by linarith)
  have he : (∑ n ∈ S, ‖(c n : ℂ)‖ * (26 / t +
      (t - 2 * Real.pi * n) ^ 2 / (2 * Real.pi * n))) ≤
      (∑ n ∈ S, c n) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hS n hn
    have ha : 0 < 2 * Real.pi * n := by positivity
    have h1 : 26 / t ≤ (1 : ℝ) / 4 := (div_le_iff₀ ht0).mpr (by linarith)
    have h2 : (t - 2 * Real.pi * n) ^ 2 / (2 * Real.pi * n) ≤ (1 : ℝ) / 4 :=
      (div_le_iff₀ ha).mpr (by linarith [hd n hn])
    rw [Complex.norm_real, Real.norm_of_nonneg (hc n hn)]
    have hmul := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (hc n hn)
    linarith
  have hcast : (∑ n ∈ S, (c n : ℂ)) = ((∑ n ∈ S, c n : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast] at hb
  have hr := unit_rotated_real_lower hκ (hb.trans he)
  linarith

end RHTower
