import GaloisForLFunctions.RHTower.Sieve.VonMangoldtBlockEstimateSharp
import GaloisForLFunctions.RHTower.Sieve.VaughanTypeIThirdDerivativeSharp

/-!
# Von Mangoldt block estimate with sharp sharp third-derivative type-I pieces

Vaughan's identity is unchanged.  Only the two type-I pieces use the third-derivative fibre
envelope; the type-II piece remains available for the existing correlation estimates.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction RHTower

noncomputable section

theorem norm_zeta_piece_third_sharp_le' {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {U V A B L : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L)
    (hKL : U * V ≤ L)
    (hcond : ∀ b ∈ Finset.Icc 1 (U * V),
      ((B - 1) / b + 1) - ((A - 1) / b + 1) - 1 ≤ ((A - 1) / b + 1)
        ∧ r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ)
        ∧ nearDiagonalLambda3 T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) :
    ‖∑ n ∈ Finset.Ico A B,
        ((((zeta : ArithmeticFunction ℝ) * truncAF vonMangoldt U
            * truncAF (moebius : ArithmeticFunction ℝ) V) n : ℝ) : ℂ) * ndPhaseExp T r n‖
      ≤ ∑ b ∈ Finset.Icc 1 (U * V),
          Real.log b * sharpThirdDerivativeFibreBound T r A B b := by
  set c : ArithmeticFunction ℝ :=
    truncAF vonMangoldt U * truncAF (moebius : ArithmeticFunction ℝ) V with hcdef
  have hassoc : ((zeta : ArithmeticFunction ℝ) * truncAF vonMangoldt U
      * truncAF (moebius : ArithmeticFunction ℝ) V) = (zeta : ArithmeticFunction ℝ) * c :=
    mul_assoc _ _ _
  rw [hassoc]
  have hterm : ∀ n ∈ Finset.Ico A B,
      ((((zeta : ArithmeticFunction ℝ) * c) n : ℝ) : ℂ) * ndPhaseExp T r n
        = (∑ p ∈ n.divisorsAntidiagonal, (1 : ℂ) * ((c p.2 : ℝ) : ℂ)) * ndPhaseExp T r n :=
    fun n hn => by rw [coe_zeta_mul_apply']
  rw [Finset.sum_congr rfl hterm]
  have hsupp : ∀ b, U * V < b → ((c b : ℝ) : ℂ) = 0 := by
    intro b hb
    rw [hcdef, truncAF_conv_apply_of_gt hb]
    simp
  refine (norm_sum_zeta_conv_ndPhaseExp_third_sharp_le' hT hr hA hB hBL hKL
    (fun b => ((c b : ℝ) : ℂ)) hsupp hcond).trans ?_
  refine Finset.sum_le_sum fun b hb => ?_
  rw [Finset.mem_Icc] at hb
  have hcoef : ‖((c b : ℝ) : ℂ)‖ ≤ Real.log b := by
    rw [Complex.norm_real, Real.norm_eq_abs, hcdef]
    exact abs_truncAF_conv_le_log U V b
  exact mul_le_mul_of_nonneg_right hcoef
    (sharpThirdDerivativeFibreBound_nonneg hT hr hb.1)

theorem norm_log_piece_third_sharp_le' {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {V A B L : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L) (hVL : V ≤ L)
    (hcond : ∀ b ∈ Finset.Icc 1 V,
      ((B - 1) / b + 1) - ((A - 1) / b + 1) - 1 ≤ ((A - 1) / b + 1)
        ∧ r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ)
        ∧ nearDiagonalLambda3 T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) :
    ‖∑ n ∈ Finset.Ico A B,
        (((ArithmeticFunction.log * truncAF (moebius : ArithmeticFunction ℝ) V) n : ℝ) : ℂ)
          * ndPhaseExp T r n‖
      ≤ ∑ b ∈ Finset.Icc 1 V,
          2 * sharpThirdDerivativeFibreBound T r A B b *
            Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ) := by
  have hterm : ∀ n ∈ Finset.Ico A B,
      (((ArithmeticFunction.log * truncAF (moebius : ArithmeticFunction ℝ) V) n : ℝ) : ℂ)
          * ndPhaseExp T r n
        = (∑ p ∈ n.divisorsAntidiagonal, ((Real.log (p.1 : ℝ) : ℝ) : ℂ)
              * ((truncAF (moebius : ArithmeticFunction ℝ) V p.2 : ℝ) : ℂ)) * ndPhaseExp T r n :=
    fun n hn => by rw [coe_log_mul_apply']
  rw [Finset.sum_congr rfl hterm]
  have hsupp : ∀ b, V < b → ((truncAF (moebius : ArithmeticFunction ℝ) V b : ℝ) : ℂ) = 0 := by
    intro b hb
    rw [truncAF_apply_of_gt hb]
    simp
  refine (norm_sum_log_conv_ndPhaseExp_third_sharp_le' hT hr hA hB hBL hVL
    (fun b => ((truncAF (moebius : ArithmeticFunction ℝ) V b : ℝ) : ℂ)) hsupp hcond).trans ?_
  refine Finset.sum_le_sum fun b hb => ?_
  have hcoef : ‖((truncAF (moebius : ArithmeticFunction ℝ) V b : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_truncAF_moebius_le_one V b
  have hterm0 : 0 ≤ 2 * sharpThirdDerivativeFibreBound T r A B b *
    Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ) := by
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have hfb : 0 ≤ sharpThirdDerivativeFibreBound T r A B b :=
      sharpThirdDerivativeFibreBound_nonneg hT hr hb1
    have hlog : 0 ≤ Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ) := by
      rcases Nat.eq_zero_or_pos ((B - 1) / b + 1 - 1) with h | h
      · rw [h]
        simp
      · exact Real.log_nonneg (by exact_mod_cast h)
    positivity
  nlinarith [hcoef, norm_nonneg ((truncAF (moebius : ArithmeticFunction ℝ) V b : ℝ) : ℂ)]

/-- Vaughan block estimate with sharp sharp third-derivative type-I envelopes. -/
theorem norm_sum_vonMangoldt_ndPhaseExp_third_sharp_le' {T r : ℝ}
    (hT : 0 < T) (hr : 0 < r) {U V A B L : ℕ}
    (hUA : U < A) (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L)
    (hKL : U * V ≤ L) (hVL : V ≤ L)
    (hcondUV : ∀ b ∈ Finset.Icc 1 (U * V),
      ((B - 1) / b + 1) - ((A - 1) / b + 1) - 1 ≤ ((A - 1) / b + 1)
        ∧ r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ)
        ∧ nearDiagonalLambda3 T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1)
    (hcondV : ∀ b ∈ Finset.Icc 1 V,
      ((B - 1) / b + 1) - ((A - 1) / b + 1) - 1 ≤ ((A - 1) / b + 1)
        ∧ r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ)
        ∧ nearDiagonalLambda3 T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) :
    ‖∑ n ∈ Finset.Ico A B, ((vonMangoldt n : ℝ) : ℂ) * ndPhaseExp T r n‖
      ≤ (∑ b ∈ Finset.Icc 1 (U * V),
            Real.log b * sharpThirdDerivativeFibreBound T r A B b)
        + (∑ b ∈ Finset.Icc 1 V,
            2 * sharpThirdDerivativeFibreBound T r A B b *
              Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ))
        + ‖∑ n ∈ Finset.Ico A B,
            (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) * ndPhaseExp T r n‖ := by
  rw [sum_vonMangoldt_block_decomp (V := V) hUA (ndPhaseExp T r)]
  refine (norm_add_le _ _).trans ?_
  refine add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) le_rfl
  · rw [norm_neg]
    exact norm_zeta_piece_third_sharp_le' hT hr hA hB hBL hKL hcondUV
  · exact norm_log_piece_third_sharp_le' hT hr hA hB hBL hVL hcondV

end

end RHTower.Sieve
