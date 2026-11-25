import GaloisForLFunctions.WindowedLandauTheory.LandauZeroFreeBounds.ExceptionalZeroBounds.NativeLocalZeros

/-! Logarithmic bounds for zero multiplicity in half-height windows on the right of the critical line. -/

open Complex Finset Metric
open WindowedLandauTheory.ZeroFreeDirichlet

noncomputable section

namespace QH.PrimeProgressions

theorem mem_half_height_right_disc {ρ : ℂ} {t : ℝ} (h₀ : 1 / 2 ≤ ρ.re) (h₁ : ρ.re ≤ 1)
    (ht : |ρ.im - t| ≤ 1 / 2) : ρ ∈ closedBall (2 + (t : ℂ) * I) (8 / 5) := by
  rw [mem_closedBall, Complex.dist_eq]
  have hr : (ρ - (2 + (t : ℂ) * I)).re = ρ.re - 2 := by simp
  have hi : (ρ - (2 + (t : ℂ) * I)).im = ρ.im - t := by simp
  have hβ : (ρ.re - 2) ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := by
    apply (sq_le_sq).mpr
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), abs_le]
    exact ⟨by linarith only [h₀], by linarith only [h₁]⟩
  have hγ : (ρ.im - t) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ht _
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [Complex.sq_norm, Complex.normSq_apply, hr, hi]
  linarith only [hβ, hγ]

/-- Two adjacent half-height windows cover every unit-height window in the right half of the strip. -/
theorem nonprincipal_half_height_right_zero_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      ∀ (Z : Finset ℂ) (t : ℝ),
        (∀ ρ ∈ Z, χ.LFunction ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ |ρ.im - t| ≤ 1 / 2) →
        (∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤ C * Real.log ((N : ℝ) * (|t| + 2)) := by
  refine ⟨4 * (16 + 2 * RHTower.pfConst), by positivity [RHTower.pfConst_pos], ?_⟩
  intro N _ χ hχ Z t hZ
  obtain ⟨W, hW, hmass, -⟩ := RHTower.L_partial_fraction_with_multiplicity_bound hχ t
  have hsub : Z ⊆ W := by
    intro ρ hρ
    obtain ⟨hzero, hre, him⟩ := hZ ρ hρ
    have hlt := RHTower.re_lt_one_of_LFunction_eq_zero hχ hzero
    change ρ ∈ (W : Set ℂ)
    rw [hW]
    exact ⟨closedBall_subset_closedBall (by norm_num) (mem_half_height_right_disc hre hlt.le him), hzero⟩
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hlog : (1 / 2 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) :=
    (by linarith [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg t]))
  have hshift := mul_le_mul_of_nonneg_left (log_height_shift N t) RHTower.pfConst_pos.le
  refine (sum_le_sum_of_subset_of_nonneg hsub (fun ρ _ _ => Nat.cast_nonneg _)).trans (hmass.trans ?_)
  nlinarith only [hlog, hshift]

end QH.PrimeProgressions
