import GaloisForLFunctions.RHTower.ZetaEulerMaclaurinArbitraryOrder
import GaloisForLFunctions.RHTower.ZetaFiniteMeanSquare

/-!
# Zeta truncation beyond the vertical height

Explicit arbitrary-order bounds for the actual zeta Dirichlet head on a dyadic
height window. The pole term and every endpoint correction are retained.
-/

open Complex Filter Topology MeasureTheory Set

noncomputable section

namespace RHTower

theorem complexRisingFactor_vertical_le {σ T t : ℝ} (hσ : 0 < σ) (hT : 1 ≤ T)
    (ht : t ∈ Icc T (2 * T)) (j : ℕ) :
    ‖complexRisingFactor ((σ : ℂ) + (t : ℂ) * I) j‖ ≤ ((σ + j + 2) * T) ^ j := by
  rw [complexRisingFactor, norm_prod]
  calc
    (∏ i ∈ Finset.range j, ‖(σ : ℂ) + (t : ℂ) * I + i‖) ≤
        ∏ _i ∈ Finset.range j, ((σ + j + 2) * T) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro i hi
      have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hij : (i : ℝ) ≤ j := by exact_mod_cast (Finset.mem_range.mp hi).le
      have heq : (σ : ℂ) + (t : ℂ) * I + i = ((σ + i : ℝ) : ℂ) + (t : ℂ) * I := by
        push_cast
        ring
      rw [heq]
      have hn := norm_add_le (((σ + i : ℝ) : ℂ)) ((t : ℂ) * I)
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ σ + i),
        abs_of_nonneg (by linarith [ht.1] : 0 ≤ t)] at hn
      nlinarith [ht.2]
    _ = _ := by simp

def zetaTruncationErrorScale (σ : ℝ) (m N : ℕ) (T : ℝ) : ℝ :=
  (N : ℝ) ^ (1 - σ) / T + (N : ℝ) ^ (-σ) / 2 +
    (∑ r ∈ Finset.range (m + 1),
      |((bernoulli (2 * r + 2) : ℚ) : ℝ)| / ((2 * r + 2).factorial : ℝ) *
        ((σ + (2 * r + 1 : ℕ) + 2) * T) ^ (2 * r + 1) *
          (N : ℝ) ^ (-σ - (2 * r + 1 : ℕ))) +
    |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / ((2 * m + 2).factorial : ℝ) *
      ((σ + (2 * m + 2 : ℕ) + 2) * T) ^ (2 * m + 2) *
        ((N : ℝ) ^ (1 - σ - (2 * m + 2 : ℕ)) / (σ + (2 * m + 2 : ℕ) - 1))

theorem zetaTruncationErrorScale_nonneg {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T)
    (m N : ℕ) : 0 ≤ zetaTruncationErrorScale σ m N T := by
  have hk : (2 : ℝ) ≤ (2 * m + 2 : ℕ) := by exact_mod_cast (by omega : 2 ≤ 2 * m + 2)
  have hden : 0 ≤ σ + (2 * m + 2 : ℕ) - 1 := by linarith
  unfold zetaTruncationErrorScale
  positivity

/-- Actual zeta minus its unsmoothed finite head, uniformly on a dyadic window. -/
theorem norm_zeta_sub_head_le_arbitraryOrder {σ T t : ℝ}
    (hσ : 0 < σ) (hT : 1 ≤ T) (ht : t ∈ Icc T (2 * T))
    {N : ℕ} (hN : 1 ≤ N) (m : ℕ) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) - zetaDirichletHead N σ t‖ ≤
      zetaTruncationErrorScale σ m N T := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    rw [hsim, Complex.one_im] at this
    linarith [ht.1]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpole : ‖(N : ℂ) ^ (1 - s) / (1 - s)‖ ≤ (N : ℝ) ^ (1 - σ) / T := by
    rw [norm_div]
    have hn : ‖(N : ℂ) ^ (1 - s)‖ = (N : ℝ) ^ (1 - σ) := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hN0]
      simp [hsre]
    rw [hn]
    apply div_le_div_of_nonneg_left (by positivity) (by linarith : 0 < T)
    have hb := Complex.abs_im_le_norm (1 - s)
    simp only [Complex.sub_im, Complex.one_im, hsim, zero_sub, abs_neg] at hb
    rw [abs_of_nonneg (by linarith [ht.1])] at hb
    exact ht.1.trans hb
  have hboundary : ‖zetaEMBoundary m s N‖ ≤ (N : ℝ) ^ (-σ) / 2 +
      ∑ r ∈ Finset.range (m + 1),
        |((bernoulli (2 * r + 2) : ℚ) : ℝ)| / ((2 * r + 2).factorial : ℝ) *
          ((σ + (2 * r + 1 : ℕ) + 2) * T) ^ (2 * r + 1) *
            (N : ℝ) ^ (-σ - (2 * r + 1 : ℕ)) := by
    unfold zetaEMBoundary
    apply (norm_add_le _ _).trans
    apply add_le_add
    · rw [norm_div, Complex.norm_ofNat, Complex.norm_cpow_eq_rpow_re_of_pos hN0]
      simp [hsre]
    · apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro r hr
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
        abs_of_pos (by positivity : 0 < ((2 * r + 2).factorial : ℝ)),
        norm_complexPowerTower s _ hN0, hsre, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right (complexRisingFactor_vertical_le hσ hT ht _)
        (by positivity)
  have hrem := norm_riemannZeta_sub_zetaEulerMaclaurinMain_le
    (show 0 < s.re by simpa [hsre]) hs1 hN m
  rw [hsre] at hrem
  have hk : (2 : ℝ) ≤ (2 * m + 2 : ℕ) := by exact_mod_cast (by omega : 2 ≤ 2 * m + 2)
  have hden : 0 ≤ σ + (2 * m + 2 : ℕ) - 1 := by linarith
  have hrem' := hrem.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (complexRisingFactor_vertical_le hσ hT ht (2 * m + 2))
      (by positivity : 0 ≤ |((bernoulli (2 * m + 2) : ℚ) : ℝ)| /
        ((2 * m + 2).factorial : ℝ))) (by positivity))
  have hid : riemannZeta s - zetaDirichletHead N σ t =
      (riemannZeta s - zetaEulerMaclaurinMain m N s) -
        (N : ℂ) ^ (1 - s) / (1 - s) - zetaEMBoundary m s N := by
    simp only [zetaEulerMaclaurinMain, zetaDirichletHead, edPoly, one_mul,
      Complex.ofReal_natCast, s]
    ring
  rw [show (σ : ℂ) + (t : ℂ) * I = s from rfl, hid]
  have hnorm := (norm_sub_le
    ((riemannZeta s - zetaEulerMaclaurinMain m N s) - (N : ℂ) ^ (1 - s) / (1 - s))
    (zetaEMBoundary m s N)).trans (add_le_add (norm_sub_le _ _) le_rfl)
  unfold zetaTruncationErrorScale
  linarith

end RHTower
