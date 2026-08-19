import GaloisForLFunctions.HTGeometry.GammaMonomialOrbitLimitBound

/-!
# An explicit majorant for the orbit series

`summable_orbitTerm` proves summability; the locally uniform M-test needs the majorant itself, with
the dependence on the base point isolated into the single factor `‖M(s)‖`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- **The orbit terms are dominated by `D‖M(s)‖(j+1)^{-2}`.** -/
theorem exists_orbitTerm_majorant {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ)
    (hdeg : ∑ k, g k = 0) (hmom : ∑ k, (g k : ℂ) * lam k = 0) :
    ∃ D Rb : ℝ, 0 ≤ D ∧ 1 ≤ Rb ∧ ∀ s : ℂ, (∑ j, |(lam j).re|) < s.re → Rb ≤ ‖s‖ →
      ∀ j : ℕ, ‖orbitTerm lam g s j‖
        ≤ D * ‖gammaMonomial lam g s‖ * (1 / ((j : ℝ) + 1) ^ 2) := by
  obtain ⟨K, Rb₀, hK0, hRb₀, hK⟩ := exists_norm_shiftRatio_sub_one_le lam g hdeg hmom
  obtain ⟨B, Rb₁, hB0, hRb₁, hB⟩ := exists_prod_norm_shiftRatio_le lam g hdeg hmom
  refine ⟨2 * K * B, max (max Rb₀ Rb₁) 1, by positivity, le_max_right _ _, ?_⟩
  intro s hs hsn j
  have hre : 0 < s.re := by
    have hnn : (0 : ℝ) ≤ ∑ j, |(lam j).re| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hs1 : (1 : ℝ) ≤ ‖s‖ := le_trans (le_max_right _ _) hsn
  have hspos : (0 : ℝ) < ‖s‖ := by linarith
  have hRb₀s : Rb₀ ≤ ‖s‖ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hsn
  have hRb₁s : Rb₁ ≤ ‖s‖ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hsn
  have hjre : (∑ i, |(lam i).re|) < (s + (j : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hjlam : ∀ k : Fin r, s + (j : ℂ) + lam k ≠ 0 := by
    intro k hcon
    have := re_pos_of_gt_sum_abs lam hjre k
    rw [hcon] at this
    simp at this
  have hjnorm : ‖s‖ ≤ ‖s + (j : ℂ)‖ := norm_le_norm_add_natCast hre j
  have hjnpos : (0 : ℝ) < ‖s + (j : ℂ)‖ := lt_of_lt_of_le hspos hjnorm
  have hpos : (0 : ℝ) < (‖s‖ + (j : ℝ)) ^ 2 := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    positivity
  have hb := hK (s + (j : ℂ)) (le_trans hRb₀s hjnorm) hjlam
  have hlow := two_mul_norm_add_natCast_sq_ge hre j
  have hb2 : ‖(∏ k, (s + (j : ℂ) + lam k) ^ (g k)) - 1‖
      ≤ 2 * K * (1 / (‖s‖ + (j : ℝ)) ^ 2) := by
    refine le_trans hb ?_
    rw [div_le_iff₀ (by positivity : (0:ℝ) < ‖s + (j : ℂ)‖ ^ 2)]
    have hratio : (1 : ℝ) ≤ 2 * ‖s + (j : ℂ)‖ ^ 2 / (‖s‖ + (j : ℝ)) ^ 2 := by
      rw [le_div_iff₀ hpos]
      linarith [hlow]
    have hfin : 2 * K * (1 / (‖s‖ + (j : ℝ)) ^ 2) * ‖s + (j : ℂ)‖ ^ 2
        = K * (2 * ‖s + (j : ℂ)‖ ^ 2 / (‖s‖ + (j : ℝ)) ^ 2) := by
      field_simp
    rw [hfin]
    nlinarith [hratio, hK0]
  have horb : ‖gammaMonomial lam g (s + (j : ℂ))‖ ≤ B * ‖gammaMonomial lam g s‖ := by
    rw [gammaMonomial_shift_nat lam g hs j, norm_mul]
    exact mul_le_mul_of_nonneg_right (hB s hs hRb₁s j) (norm_nonneg _)
  have hnn4 : (0 : ℝ) ≤ 2 * K * (1 / (‖s‖ + (j : ℝ)) ^ 2) := by
    have h1 : (0 : ℝ) ≤ 1 / (‖s‖ + (j : ℝ)) ^ 2 := by positivity
    nlinarith [hK0, h1]
  have hstep : ‖orbitTerm lam g s j‖
      ≤ (2 * K * (1 / (‖s‖ + (j : ℝ)) ^ 2)) * (B * ‖gammaMonomial lam g s‖) := by
    rw [orbitTerm, norm_mul]
    exact mul_le_mul hb2 horb (norm_nonneg _) hnn4
  have hshrink : (1 : ℝ) / (‖s‖ + (j : ℝ)) ^ 2 ≤ 1 / ((j : ℝ) + 1) ^ 2 := by
    have h1 : ((j : ℝ) + 1) ^ 2 ≤ (‖s‖ + (j : ℝ)) ^ 2 := by
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ ‖s‖ + 2 * (j : ℝ) + 1)
        (by linarith : (0:ℝ) ≤ ‖s‖ - 1)]
    exact one_div_le_one_div_of_le (by positivity) h1
  calc ‖orbitTerm lam g s j‖
      ≤ (2 * K * (1 / (‖s‖ + (j : ℝ)) ^ 2)) * (B * ‖gammaMonomial lam g s‖) := hstep
    _ ≤ (2 * K * (1 / ((j : ℝ) + 1) ^ 2)) * (B * ‖gammaMonomial lam g s‖) := by
        have hnn : (0 : ℝ) ≤ B * ‖gammaMonomial lam g s‖ := by positivity
        have h2K : (0 : ℝ) ≤ 2 * K := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hshrink h2K) hnn
    _ = 2 * K * B * ‖gammaMonomial lam g s‖ * (1 / ((j : ℝ) + 1) ^ 2) := by ring

theorem summable_inv_succ_sq : Summable (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1) ^ 2) := by
  have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
  have h2 := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr h
  refine h2.congr fun j => ?_
  push_cast
  ring

end

end GaloisForLFunctions.HTGeometry
