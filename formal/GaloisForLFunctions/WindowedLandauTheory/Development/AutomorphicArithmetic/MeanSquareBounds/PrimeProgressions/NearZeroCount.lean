import GaloisForLFunctions.WindowedLandauTheory.LandauZeroFreeBounds.ExceptionalZeroBounds.NativeLocalZeros

/-! The sum of the zero multiplicities near the right edge of the critical strip. -/

open Complex Finset Metric RHTower
open WindowedLandauTheory.ZeroFreeDirichlet

noncomputable section

namespace QH.PrimeProgressions

/-- At any height, the multiplicities in a unit neighborhood near `Re s = 1`
sum to at most a constant times the logarithm of conductor times height. -/
theorem nonprincipal_near_zero_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      ∀ (Z : Finset ℂ) (t : ℝ),
        (∀ ρ ∈ Z, χ.LFunction ρ = 0 ∧ 19 / 20 ≤ ρ.re ∧ |ρ.im - t| ≤ 1) →
        (∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤ C * Real.log ((N : ℝ) * (|t| + 2)) := by
  refine ⟨4 * (16 + 2 * pfConst), by positivity [pfConst_pos], ?_⟩
  intro N _ χ hχ Z t hZ
  obtain ⟨W, hW, hmass, -⟩ := L_partial_fraction_with_multiplicity_bound hχ t
  have hsub : Z ⊆ W := by
    intro ρ hρ
    obtain ⟨hzero, hre, him⟩ := hZ ρ hρ
    have hlt := re_lt_one_of_LFunction_eq_zero hχ hzero
    change ρ ∈ (W : Set ℂ)
    rw [hW]
    refine ⟨?_, hzero⟩
    rw [mem_closedBall, Complex.dist_eq]
    have hr : (ρ - (2 + (t : ℂ) * I)).re = ρ.re - 2 := by simp
    have hi : (ρ - (2 + (t : ℂ) * I)).im = ρ.im - t := by simp
    have hβ : (ρ.re - 2) ^ 2 ≤ (21 / 20 : ℝ) ^ 2 := by
      apply (sq_le_sq).mpr
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 21 / 20), abs_le]
      exact ⟨by linarith only [hre], by linarith only [hlt]⟩
    have hγ : (ρ.im - t) ^ 2 ≤ 1 := by
      rw [← sq_abs, ← one_pow 2]
      exact pow_le_pow_left₀ (abs_nonneg _) him _
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp
    rw [Complex.sq_norm, Complex.normSq_apply, hr, hi]
    nlinarith only [hβ, hγ]
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hlog : (1 / 2 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) :=
    (by linarith [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg t]))
  have hshift := mul_le_mul_of_nonneg_left (log_height_shift N t) pfConst_pos.le
  refine (sum_le_sum_of_subset_of_nonneg hsub (fun ρ _ _ => Nat.cast_nonneg _)).trans (hmass.trans ?_)
  nlinarith only [hlog, hshift]

end QH.PrimeProgressions
