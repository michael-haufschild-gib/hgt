import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExplicitFormula.HurwitzTailGrowth
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroRepulsion.CharacterGrowth

/-! Conductor-uniform growth in a strip crossing the imaginary axis, after removing the principal pole. -/

open Complex DirichletCharacter Finset

open scoped Classical

noncomputable section

namespace QH.PrimeProgressions

private theorem toAddCircle_positive_rep (N : ℕ) [NeZero N] (j : ZMod N) :
    ∃ a : ℝ, 1 / (N : ℝ) ≤ a ∧ a ≤ 1 ∧ (a : UnitAddCircle) = j.toAddCircle := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos _)
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  rcases eq_or_ne j 0 with rfl | hj
  · exact ⟨1, (div_le_one hN).mpr hN₁, le_rfl, by rw [map_zero]; exact AddCircle.coe_period (1 : ℝ)⟩
  · refine ⟨j.val / N, div_le_div_of_nonneg_right ?_ hN.le, (div_le_one hN).mpr ?_,
      j.toAddCircle_apply.symm⟩
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hj ((ZMod.val_eq_zero j).mp h))
    · exact_mod_cast (ZMod.val_lt j).le

private theorem norm_pole_removed_mul_LFunction (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ) (hs : -(49 / 50 : ℝ) ≤ s.re) (hs₀ : s.re ≤ 1 / 2) :
    ‖(s - 1) * χ.LFunction s‖ ≤ 13 * (N : ℝ) ^ 3 * (‖s‖ + 1) ^ 3 := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos _)
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have hn : ‖(N : ℂ) ^ (-s)‖ ≤ N := by
    rw [norm_natCast_cpow_of_pos (NeZero.pos N), neg_re]
    exact (Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith only [hs] : -s.re ≤ 1)).trans_eq
      (Real.rpow_one _)
  change ‖(s - 1) * ((N : ℂ) ^ (-s) * ∑ j : ZMod N, χ j * HurwitzZeta.hurwitzZeta j.toAddCircle s)‖ ≤ _
  rw [mul_left_comm, mul_sum, norm_mul]
  calc
    _ ≤ (N : ℝ) * ∑ j : ZMod N, ‖(s - 1) * (χ j * HurwitzZeta.hurwitzZeta j.toAddCircle s)‖ :=
      mul_le_mul hn (norm_sum_le _ _) (norm_nonneg _) hN.le
    _ ≤ (N : ℝ) * ∑ _j : ZMod N, (13 * (N : ℝ) * (‖s‖ + 1) ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ hN.le
      apply sum_le_sum
      intro j _
      obtain ⟨a, ha, ha₁, hj⟩ := toAddCircle_positive_rep N j
      have ha₀ : 0 < a := (by positivity : 0 < 1 / (N : ℝ)).trans_le ha
      have hI : a⁻¹ ≤ N := by
        have h := one_div_le_one_div_of_le (by positivity : 0 < 1 / (N : ℝ)) ha
        simpa only [one_div, inv_inv] using h
      rw [mul_left_comm, norm_mul, ← hj]
      exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one j)).trans
        ((norm_hurwitzZeta_pole_removed ha₀ ha₁ hs hs₀).trans (by gcongr))
    _ = _ := by
      simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
      ring

/-- The Dirichlet function with its principal pole removed. -/
def entireCharacterL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  if χ = 1 then LFunctionTrivChar₁ N else χ.LFunction

theorem differentiable_entireCharacterL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Differentiable ℂ (entireCharacterL χ) := by
  unfold entireCharacterL
  split_ifs with h
  · exact differentiable_LFunctionTrivChar₁ N
  · exact differentiable_LFunction h

theorem norm_entireCharacterL_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ) (hs : -(49 / 50 : ℝ) ≤ s.re) :
    ‖entireCharacterL χ s‖ ≤ 26 * (N : ℝ) ^ 3 * (‖s‖ + 1) ^ 3 := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have hR : 1 ≤ ‖s‖ + 1 := by linarith only [norm_nonneg s]
  have hN₃ : (N : ℝ) ≤ (N : ℝ) ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hN (show 1 ≤ (3 : ℕ) by decide)
  have hR₂ : (‖s‖ + 1) ^ 2 ≤ (‖s‖ + 1) ^ 3 := pow_le_pow_right₀ hR (by decide)
  unfold entireCharacterL
  split_ifs with hχ
  · subst χ
    by_cases h : 1 / 2 ≤ s.re
    · refine (dhl_triv_growth N s h).trans ?_
      rw [add_comm 1 ‖s‖]
      gcongr <;> norm_num
    · rw [LFunctionTrivChar₁, Function.update_of_ne (fun e => h (by norm_num [e]))]
      exact (norm_pole_removed_mul_LFunction N 1 s hs (le_of_not_ge h)).trans (by gcongr <;> norm_num)
  · by_cases h : 1 / 2 ≤ s.re
    · have hb := Zeta23.ThmE.LFunction_linear_growth hχ (by norm_num : (0 : ℝ) < 1 / 2) h
      norm_num at hb
      have hI : |s.im| + 1 ≤ (‖s‖ + 1) ^ 3 :=
        (add_le_add (abs_im_le_norm s) le_rfl).trans (by
          simpa only [pow_one] using pow_le_pow_right₀ hR (show 1 ≤ (3 : ℕ) by decide))
      refine hb.trans ?_
      calc
        (N : ℝ) * 3 * (|s.im| + 1) = 3 * N * (|s.im| + 1) := by ring
        _ ≤ _ := by gcongr <;> norm_num
    · have hm : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
        have he := (neg_le_abs (s - 1).re).trans (abs_re_le_norm (s - 1))
        rw [sub_re, one_re] at he
        linarith only [he, le_of_not_ge h]
      have hb := norm_pole_removed_mul_LFunction N χ s hs (le_of_not_ge h)
      rw [norm_mul] at hb
      have he := mul_le_mul_of_nonneg_right hm (norm_nonneg (χ.LFunction s))
      linarith only [he, hb]

end QH.PrimeProgressions
