import Mathlib

/-! Normalized reciprocal moments of points in a right half-plane. -/

open Finset Complex

noncomputable section

namespace QH.PrimeProgressions.DHF

theorem u_disc (η : ℝ) (hη : 0 < η) (w : ℂ) (hw : η ≤ w.re) :
    ‖(η : ℂ) / w‖ ^ 2 ≤ ((η : ℂ) / w).re := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw
    linarith
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.2 hw0
  rw [norm_div, div_pow, Complex.sq_norm, Complex.sq_norm, Complex.div_re, Complex.normSq_ofReal,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  have h1 : η * η ≤ η * w.re := mul_le_mul_of_nonneg_left hw hη.le
  simp only [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hn.le)

theorem u_sum_re (η : ℝ) {N : ℕ} (w : Fin N → ℂ) (j : ℕ) :
    (∑ i, ((η : ℂ) / w i) ^ j).re = η ^ j * (∑ i, 1 / (w i) ^ j).re := by
  have h : ∑ i, ((η : ℂ) / w i) ^ j = ((η ^ j : ℝ) : ℂ) * ∑ i, 1 / (w i) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [div_pow, div_eq_mul_one_div, Complex.ofReal_pow]
  rw [h, Complex.re_ofReal_mul]

end QH.PrimeProgressions.DHF
