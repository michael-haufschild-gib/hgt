import GaloisForLFunctions.RHTower.Sieve.ZetaTruncated

/-!
# Truncation keeping the partial sum intact

The corpus truncation bound replaces the finite sum by the sum of the moduli of its terms, which
discards all cancellation and can only ever give the trivial logarithmic size.  For an estimate that
exploits cancellation the sum has to survive as a complex sum.

This is the same identity bounded one step earlier: the tail terms are estimated as before, but the
head is left as `‖∑_{k ≤ N} k^{-w}‖`.  Any bound on that partial sum — in particular the derivative
test chain on the line `Re s = 1` — then transfers directly to `ζ`.
-/

namespace RHTower.Sieve

open MeasureTheory Set

/-- **Truncation with the partial sum intact.**  Only the tail terms are estimated. -/
theorem norm_riemannZeta_le_partialSum {w : ℂ} (hw0 : 0 < w.re) (hwne1 : w ≠ 1) {N : ℕ}
    (hN : 1 ≤ N) :
    ‖riemannZeta w‖
      ≤ ‖∑ k ∈ Finset.Icc 1 N, ((k : ℝ) : ℂ) ^ (-w)‖
        + (N : ℝ) ^ (1 - w.re) / ‖w - 1‖
        + ‖w‖ * ((N : ℝ) ^ (-w.re) / w.re) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  rw [riemannZeta_eq_sum_add_tail hw0 hwne1 hN]
  refine le_trans (norm_sub_le _ _) ?_
  refine add_le_add ?_ ?_
  · refine le_trans (norm_add_le _ _) ?_
    refine add_le_add (le_refl _) ?_
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hN0]
    have hre : ((1 : ℂ) - w).re = 1 - w.re := by simp
    rw [hre]
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_integral_Ioi_fract_cpow_le hw0 hN) (norm_nonneg w)

/-- **On the line `Re s = 1`.**  The two tail terms are `1/|t|` and `‖1 + it‖/N`. -/
theorem norm_riemannZeta_one_add_I_mul_le {t : ℝ} (ht : 0 < t) {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta (1 + Complex.I * (t : ℂ))‖
      ≤ ‖∑ k ∈ Finset.Icc 1 N, ((k : ℝ) : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖
        + 1 / t + ‖(1 : ℂ) + Complex.I * (t : ℂ)‖ / (N : ℝ) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hre : ((1 : ℂ) + Complex.I * (t : ℂ)).re = 1 := by simp
  have hw0 : 0 < ((1 : ℂ) + Complex.I * (t : ℂ)).re := by rw [hre]; norm_num
  have hsub : (1 : ℂ) + Complex.I * (t : ℂ) - 1 = Complex.I * (t : ℂ) := by ring
  have hnormsub : ‖(1 : ℂ) + Complex.I * (t : ℂ) - 1‖ = t := by
    rw [hsub, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht]
  have hwne1 : (1 : ℂ) + Complex.I * (t : ℂ) ≠ 1 := by
    intro hcon
    rw [hcon] at hnormsub
    simp at hnormsub
    exact absurd hnormsub.symm (ne_of_gt ht)
  refine le_trans (norm_riemannZeta_le_partialSum hw0 hwne1 hN) ?_
  refine add_le_add (add_le_add (le_refl _) ?_) ?_
  · rw [hnormsub, hre]
    have : (N : ℝ) ^ (1 - (1 : ℝ)) = 1 := by norm_num
    rw [this]
  · rw [hre]
    have hpow : (N : ℝ) ^ (-(1 : ℝ)) = 1 / (N : ℝ) := by
      rw [Real.rpow_neg_one, one_div]
    rw [hpow]
    have : (1 : ℝ) / (N : ℝ) / 1 = 1 / (N : ℝ) := by ring
    rw [this]
    exact le_of_eq (by ring)

end RHTower.Sieve
