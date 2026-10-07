import GaloisForLFunctions.Bottcher.ModularLambdaProperness
import GaloisForLFunctions.HTGeometry.ModularDiskChart

/-!
# Height bounds for modular reduction and the disk chart

Reduction to a fundamental domain cannot increase height beyond the maximum
of the original height and its reciprocal. The disk chart controls both.
-/

open Complex UpperHalfPlane
open scoped MatrixGroups

namespace Bottcher

private theorem intCast_sq_ge_one {n : ℤ} (hn : n ≠ 0) :
    (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
  have h : n ≤ -1 ∨ 1 ≤ n := by omega
  rcases h with h | h
  · have : (n : ℝ) ≤ -1 := by exact_mod_cast h
    nlinarith [sq_nonneg ((n : ℝ) + 1)]
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h
    nlinarith [sq_nonneg ((n : ℝ) - 1)]

/-- An integral modular transformation has a uniform height bound. -/
theorem modular_smul_im_le_max (g : SL(2, ℤ)) (τ : ℍ) :
    (g • τ).im ≤ max τ.im (1 / τ.im) := by
  have hdenpos : 0 < Complex.normSq (denom g τ) := normSq_denom_pos g τ.im_ne_zero
  rw [ModularGroup.im_smul_eq_div_normSq]
  by_cases hc : g 1 0 = 0
  · have hd : g 1 1 ≠ 0 := by
      intro hd
      have hh := g.det_coe
      rw [Matrix.det_fin_two] at hh
      simp only [hc, hd, mul_zero, sub_self] at hh
      exact zero_ne_one hh
    have hden : 1 ≤ Complex.normSq (denom g τ) := by
      have heq : Complex.normSq (denom g τ) = (g 1 1 : ℝ) ^ 2 := by
        simp [ModularGroup.denom_apply, hc, Complex.normSq_apply, pow_two]
      rw [heq]
      exact intCast_sq_ge_one hd
    apply le_trans ?_ (le_max_left _ _)
    rw [div_le_iff₀ hdenpos]
    nlinarith [τ.im_pos]
  · have hcsq := intCast_sq_ge_one hc
    have hdim : (denom g τ).im = (g 1 0 : ℝ) * τ.im := by
      simp [ModularGroup.denom_apply]
    have hden : τ.im ^ 2 ≤ Complex.normSq (denom g τ) := by
      rw [Complex.normSq_apply, hdim]
      nlinarith [mul_le_mul_of_nonneg_right hcsq (sq_nonneg τ.im),
        sq_nonneg (denom g τ).re]
    apply le_trans ?_ (le_max_right _ _)
    rw [div_le_div_iff₀ hdenpos τ.im_pos]
    nlinarith

/-- Fundamental-domain representatives lie above the floor used for the theta estimates. -/
theorem im_ge_four_fifths_of_mem_fd {τ : ℍ} (hτ : τ ∈ ModularGroup.fd) :
    (4 : ℝ) / 5 ≤ τ.im := by
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hτ
  have hp := τ.im_pos
  by_contra hn
  have ht : τ.im < 4 / 5 := lt_of_not_ge hn
  nlinarith

/-- Both height and reciprocal height are controlled by distance from the disk boundary. -/
theorem cayleyInv_height_max_le {z : ℂ} (hz : ‖z‖ < 1) :
    max (cayleyInv z).im (1 / (cayleyInv z).im) ≤ 4 / (1 - ‖z‖ ^ 2) := by
  have hzne : z ≠ 1 := by intro h; simp [h] at hz
  have hy := cayleyInv_im_pos_of_norm_lt_one hz
  have hD : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hzne.symm
  have hN : 0 < ‖1 - z‖ ^ 2 := by positivity
  have hlow : 1 - ‖z‖ ≤ ‖1 - z‖ := by
    simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) z
  have hupp : ‖1 - z‖ ≤ 1 + ‖z‖ := by
    simpa only [norm_one] using norm_sub_le (1 : ℂ) z
  have hsqlo : (1 - ‖z‖) ^ 2 ≤ ‖1 - z‖ ^ 2 :=
    pow_le_pow_left₀ (by linarith) hlow 2
  have hsqhi : ‖1 - z‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (1 - z)]
  have hform : (cayleyInv z).im = (1 - ‖z‖ ^ 2) / ‖1 - z‖ ^ 2 := by
    rw [cayleyInv_im_eq_diskPoissonOne hzne, diskPoissonOne]
  apply max_le
  · rw [hform, div_le_div_iff₀ hN hD]
    have hplus : (1 + ‖z‖) ^ 2 ≤ 4 := by nlinarith [norm_nonneg z]
    have hm := mul_le_mul_of_nonneg_right hplus (sq_nonneg (1 - ‖z‖))
    nlinarith [hsqlo]
  · rw [hform, one_div_div]
    exact div_le_div_of_nonneg_right hsqhi hD.le

end Bottcher
