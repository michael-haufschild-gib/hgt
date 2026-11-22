import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.SmoothedBoxTail

/-! A zero-free box bounds the logarithmic derivative at one by a log-log term. -/

open Complex Finset Filter ArithmeticFunction WindowedLandauTheory.HC
open GaloisForLFunctions.ShortIntervalPrimesInProgressions

namespace QH

private theorem norm_partialLogDerivative_le {N : ℕ} (χ : DirichletCharacter ℂ N)
    {z : ℝ} (hz : 1 ≤ z) :
    ‖partialLogDerivative χ z‖ ≤ Real.log z + (Real.log 4 + 4) := by
  unfold partialLogDerivative
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n _ => ?_).trans
    (WindowedLandauTheory.sum_Icc_vonMangoldt_div_le hz))
  rw [twistedVM, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg,
    Complex.norm_natCast]
  rw [mul_comm ‖χ (n : ZMod N)‖]
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_right vonMangoldt_nonneg (χ.norm_le_one _)) (Nat.cast_nonneg n)

/-- Truncation at `(log Q)^800` puts the difference quotient well inside the box
and makes its error at most one for large `Q`. -/
theorem logDerivativeAtOne_le_loglog :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      L₀ ≤ Real.log Q → χ.IsPrimitive → GoodC Q χ →
      ‖An.logDerivativeAtOne χ‖ ≤ 800 * Real.log (Real.log Q) + (Real.log 4 + 5) := by
  let C : ℝ := 2 * 50000000 * 801 ^ 2
  have hC : 0 < C := by norm_num [C]
  have hpow := (Real.tendsto_exp_div_pow_atTop 6401).eventually_ge_atTop 1
  have hlog := (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1)).bound
    (c := 1 / C) (by positivity)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp ((eventually_ge_atTop (Real.exp 1 + 3)).and (hpow.and hlog))
  have hL₀' : 1 ≤ L₀ := (by linarith only [Real.exp_pos (1 : ℝ)] : 1 ≤ Real.exp 1 + 3).trans
    (hL₀ L₀ le_rfl).1
  refine ⟨L₀, hL₀', fun Q N _ χ hL hp ⟨hχ, hN, hbox⟩ => ?_⟩
  let L := Real.log Q
  let z := L ^ (800 : ℕ)
  obtain ⟨hL₃, hE, hsmall⟩ := hL₀ L hL
  have hLpos : 0 < L := by linarith only [hL₃, Real.exp_pos (1 : ℝ)]
  have hL₁ : 1 ≤ L := hL₀'.trans hL
  have hLlog : 1 ≤ Real.log L :=
    (Real.le_log_iff_exp_le hLpos).mpr (by linarith only [hL₃])
  have hQpos : 0 < Q := (by exact_mod_cast NeZero.pos N : (0 : ℝ) < N).trans_le hN
  have hz : 2 ≤ z :=
    (by linarith only [hL₃, Real.exp_pos (1 : ℝ)] : 2 ≤ L).trans (le_self_pow₀ hL₁ (by norm_num))
  have hzQ : z ^ 8 + 2 ≤ Q := by
    rw [le_div_iff₀ (by positivity), one_mul] at hE
    have hE' : L ^ 6401 ≤ Q := by simpa only [L, Real.exp_log hQpos] using hE
    dsimp [z]
    rw [← pow_mul]
    change L ^ 6400 + 2 ≤ Q
    refine le_trans ?_ hE'
    rw [pow_succ']
    have h := mul_le_mul_of_nonneg_right (show (3 : ℝ) ≤ L by
      linarith only [hL₃, Real.exp_pos (1 : ℝ)]) (show 0 ≤ L ^ (6400 : ℕ) by positivity)
    have hL8 : 1 ≤ L ^ (6400 : ℕ) := one_le_pow₀ hL₁
    linarith only [h, hL8]
  have hzt : Real.log z = 800 * Real.log L := by
    dsimp [z]
    rw [Real.log_pow]
    norm_num
  have hzpow : z ^ (-1 / 400 : ℝ) = (L ^ 2)⁻¹ := by
    rw [show z = L ^ (800 : ℝ) from (Real.rpow_natCast L 800).symm, ← Real.rpow_mul hLpos.le,
      show (800 : ℝ) * (-1 / 400) = -(2 : ℝ) by norm_num, Real.rpow_neg hLpos.le, Real.rpow_two]
  have hrel : ‖partialLogDerivative χ z + An.logDerivativeAtOne χ‖ ≤ 1 := by
    refine (norm_partialLogDerivative_error_le hχ hp hbox hz hzQ).trans ?_
    rw [hzpow, ← div_eq_mul_inv, div_le_one (by positivity)]
    have hNL := Real.log_le_log (by exact_mod_cast NeZero.pos N) hN
    rw [Real.rpow_two, Real.rpow_one, Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg hLpos.le, one_div, inv_mul_eq_div, le_div_iff₀ hC] at hsmall
    have hl : 1 + Real.log z ≤ 801 * Real.log L := by linarith only [hzt, hLlog]
    have hzlog : 0 ≤ 1 + Real.log z := by have := Real.log_nonneg (one_le_two.trans hz); linarith
    calc 50000000 * (1 + Real.log N) * (1 + Real.log z) ^ 2
        ≤ 50000000 * (2 * L) * (801 * Real.log L) ^ 2 := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (by linarith only [hNL, hL₁]) (by norm_num)
          · exact pow_le_pow_left₀ hzlog hl 2
          · positivity
          · positivity
      _ = (Real.log L ^ 2 * C) * L := by dsimp [C]; ring
      _ ≤ _ := by simpa only [sq] using mul_le_mul_of_nonneg_right hsmall hLpos.le
  calc ‖An.logDerivativeAtOne χ‖
      = ‖(partialLogDerivative χ z + An.logDerivativeAtOne χ) - partialLogDerivative χ z‖ := by
        rw [add_sub_cancel_left]
    _ ≤ ‖partialLogDerivative χ z + An.logDerivativeAtOne χ‖ + ‖partialLogDerivative χ z‖ :=
        norm_sub_le _ _
    _ ≤ _ := by
      have hP := norm_partialLogDerivative_le χ (one_le_two.trans hz)
      linarith only [hrel, hP, hzt]

theorem kappa4 :
    ∀ ε A : ℝ, 0 < ε → ε < 1 / 52 → 0 < A → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀,
      ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
        Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ A * Y ^ (ε / 5) * Real.log Y ^ 2 →
        χ.IsPrimitive → GoodC Q χ → ‖An.logDerivativeAtOne χ‖ ≤ 4 * Real.log Y := by
  intro ε A hε hε' hA
  obtain ⟨L₀, hL₀, hbound⟩ := logDerivativeAtOne_le_loglog
  have hlo := (tendsto_rpow_atTop (by positivity : 0 < ε / 6)).eventually_ge_atTop L₀
  have hsmall := Real.isLittleO_log_id_atTop.bound (c := 1 / 4000) (by norm_num)
  have hconst := eventually_ge_atTop (4 * (800 * Real.log A + (Real.log 4 + 5)))
  have hYlog := Real.tendsto_log_atTop.eventually ((eventually_ge_atTop 1).and (hsmall.and hconst))
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp
    ((eventually_gt_atTop (0 : ℝ)).and (hlo.and hYlog))
  refine ⟨Y₀, fun Y hY Q N _ χ hQlo hQhi hp hg => ?_⟩
  obtain ⟨hYpos, hlo', hlog, hsmall', hconst'⟩ := hY₀ Y hY
  have hl : 0 < Real.log Y := zero_lt_one.trans_le hlog
  have hlogQ := (Real.log_le_log (zero_lt_one.trans_le (hL₀.trans (hlo'.trans hQlo))) hQhi)
  have hpow : 0 < Y ^ (ε / 5) := Real.rpow_pos_of_pos hYpos _
  rw [Real.log_mul (mul_pos hA hpow).ne' (by positivity), Real.log_mul hA.ne' hpow.ne',
    Real.log_rpow hYpos, Real.log_pow] at hlogQ
  push_cast at hlogQ
  dsimp only [id] at hsmall'
  rw [Real.norm_of_nonneg (Real.log_nonneg hlog), Real.norm_of_nonneg hl.le] at hsmall'
  have hrate := mul_le_mul_of_nonneg_right hε'.le hl.le
  have h := hbound Q N χ (hlo'.trans hQlo) hp hg
  linarith only [h, hlogQ, hsmall', hconst', hrate, hlog]

end QH
