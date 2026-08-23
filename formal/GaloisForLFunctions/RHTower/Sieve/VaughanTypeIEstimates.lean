import GaloisForLFunctions.RHTower.Sieve.VaughanTypeIPieces

/-!
# The two type-I pieces of Vaughan's identity, estimated

Each is a `ζ`- or `log`-convolution summed against `e(F(n))` over the block, so the fibre estimates
apply directly; the coefficient bounds of the previous file then remove the arithmetic functions.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction RHTower

noncomputable section

/-- **The first type-I piece.** -/
theorem norm_zeta_piece_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {U V A B L : ℕ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L)
    (hcond : ∀ b ∈ Finset.Icc 1 L,
      r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ)
        ∧ nearDiagonalLambda T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) :
    ‖∑ n ∈ Finset.Ico A B,
        ((((zeta : ArithmeticFunction ℝ) * truncAF vonMangoldt U
            * truncAF (moebius : ArithmeticFunction ℝ) V) n : ℝ) : ℂ) * ndPhaseExp T r n‖
      ≤ ∑ b ∈ Finset.Icc 1 L, Real.log b * fibreBound T r A B b := by
  set c : ArithmeticFunction ℝ :=
    truncAF vonMangoldt U * truncAF (moebius : ArithmeticFunction ℝ) V with hcdef
  have hassoc : ((zeta : ArithmeticFunction ℝ) * truncAF vonMangoldt U
      * truncAF (moebius : ArithmeticFunction ℝ) V)
      = (zeta : ArithmeticFunction ℝ) * c := mul_assoc _ _ _
  rw [hassoc]
  have hterm : ∀ n ∈ Finset.Ico A B,
      ((((zeta : ArithmeticFunction ℝ) * c) n : ℝ) : ℂ) * ndPhaseExp T r n
        = (∑ p ∈ n.divisorsAntidiagonal, (1 : ℂ) * ((c p.2 : ℝ) : ℂ)) * ndPhaseExp T r n :=
    fun n _ => by rw [coe_zeta_mul_apply']
  rw [Finset.sum_congr rfl hterm]
  refine le_trans
    (norm_sum_zeta_conv_ndPhaseExp_le hT hr hA hB hBL (fun b => ((c b : ℝ) : ℂ)) hcond) ?_
  refine Finset.sum_le_sum fun b hb => ?_
  rw [Finset.mem_Icc] at hb
  have hcoef : ‖((c b : ℝ) : ℂ)‖ ≤ Real.log b := by
    rw [Complex.norm_real, Real.norm_eq_abs, hcdef]
    exact abs_truncAF_conv_le_log U V b
  have hfb : (0 : ℝ) ≤ fibreBound T r A B b := by
    rw [fibreBound]
    positivity
  exact mul_le_mul_of_nonneg_right hcoef hfb

/-- **The second type-I piece.** -/
theorem norm_log_piece_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {V A B L : ℕ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L)
    (hcond : ∀ b ∈ Finset.Icc 1 L,
      r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ)
        ∧ nearDiagonalLambda T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) :
    ‖∑ n ∈ Finset.Ico A B,
        (((ArithmeticFunction.log * truncAF (moebius : ArithmeticFunction ℝ) V) n : ℝ) : ℂ)
          * ndPhaseExp T r n‖
      ≤ ∑ b ∈ Finset.Icc 1 L,
          2 * fibreBound T r A B b * Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ) := by
  have hterm : ∀ n ∈ Finset.Ico A B,
      (((ArithmeticFunction.log * truncAF (moebius : ArithmeticFunction ℝ) V) n : ℝ) : ℂ)
          * ndPhaseExp T r n
        = (∑ p ∈ n.divisorsAntidiagonal, ((Real.log (p.1 : ℝ) : ℝ) : ℂ)
              * ((truncAF (moebius : ArithmeticFunction ℝ) V p.2 : ℝ) : ℂ)) * ndPhaseExp T r n :=
    fun n _ => by rw [coe_log_mul_apply']
  rw [Finset.sum_congr rfl hterm]
  refine le_trans (norm_sum_log_conv_ndPhaseExp_le hT hr hA hB hBL
    (fun b => ((truncAF (moebius : ArithmeticFunction ℝ) V b : ℝ) : ℂ)) hcond) ?_
  refine Finset.sum_le_sum fun b hb => ?_
  have hcoef : ‖((truncAF (moebius : ArithmeticFunction ℝ) V b : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_truncAF_moebius_le_one V b
  have hfb : (0 : ℝ) ≤ fibreBound T r A B b := by
    rw [fibreBound]
    positivity
  have hlog : (0 : ℝ) ≤ Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ) := by
    rcases Nat.eq_zero_or_pos ((B - 1) / b + 1 - 1) with h | h
    · rw [h]
      simp
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hprod : (0 : ℝ) ≤ 2 * fibreBound T r A B b * Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ) := by
    positivity
  nlinarith [hcoef, hprod, norm_nonneg ((truncAF (moebius : ArithmeticFunction ℝ) V b : ℝ) : ℂ)]

end

end RHTower.Sieve
