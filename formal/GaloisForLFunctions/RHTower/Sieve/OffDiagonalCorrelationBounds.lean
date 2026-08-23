import GaloisForLFunctions.RHTower.Sieve.PairSumSplit

/-!
# Off-diagonal correlation bounds on a dyadic block

The correlation attached to a pair `(m₁, m₂)` runs over a sub-interval of the block, so both
regimes apply with the block's own endpoints after one monotonicity step.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction RHTower

noncomputable section

/-- **The off-diagonal correlation, second-derivative regime.** -/
theorem norm_masked_correlation_offdiag_secondDeriv_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B P Q : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P) {m₁ m₂ : ℕ}
    (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (hne : m₁ ≠ m₂)
    (h4₁ : 4 * (r / m₁) ≤ (P : ℝ)) (h4₂ : 4 * (r / m₂) ≤ (P : ℝ))
    (hlam : curvedLambda (T * |r / m₁ - r / m₂|) (P : ℝ) ≤ 1) :
    ‖∑ d ∈ Finset.Ico P Q,
        maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖
      ≤ 2500 * Real.sqrt (T * |r / m₁ - r / m₂| / (36 * Real.pi * P))
        + 22 * Real.sqrt (36 * Real.pi / (T * |r / m₁ - r / m₂|))
            * Real.sqrt (((Q : ℝ)) ^ 3) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set P' : ℕ := max P (max ((A - 1) / m₁ + 1) ((A - 1) / m₂ + 1)) with hP'
  set Q' : ℕ := min Q (min ((B - 1) / m₁ + 1) ((B - 1) / m₂ + 1)) with hQ'
  have hPP' : P ≤ P' := le_max_left _ _
  have hQQ' : Q' ≤ Q := min_le_left _ _
  have hP'1 : 1 ≤ P' := le_trans hP hPP'
  have hP'r : (P : ℝ) ≤ (P' : ℝ) := by exact_mod_cast hPP'
  have hQ'r : (Q' : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQQ'
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hY0 : (0 : ℝ) ≤ T * |r / m₁ - r / m₂| := by positivity
  rw [sum_masked_correlation_eq hA hB hP T r hm₁ hm₂, ← hP', ← hQ']
  have hlam' : curvedLambda (T * |r / m₁ - r / m₂|) ((P' : ℕ) : ℝ) ≤ 1 := by
    rcases eq_or_lt_of_le hY0 with hzero | hpos
    · rw [curvedLambda, ← hzero]
      norm_num
    · exact le_trans (curvedLambda_anti hpos hP0 hP'r) hlam
  have hmain := norm_sum_corr_le (B := Q') hT hr hm₁ hm₂ hne hP'1
    (le_trans h4₁ hP'r) (le_trans h4₂ hP'r) hlam'
  refine hmain.trans ?_
  have hfirst : Real.sqrt (T * |r / m₁ - r / m₂| / (36 * Real.pi * (P' : ℝ)))
      ≤ Real.sqrt (T * |r / m₁ - r / m₂| / (36 * Real.pi * (P : ℝ))) := by
    refine Real.sqrt_le_sqrt ?_
    refine div_le_div_of_nonneg_left hY0 (by positivity) ?_
    have : (36 : ℝ) * Real.pi * (P : ℝ) ≤ 36 * Real.pi * (P' : ℝ) := by
      have : (0 : ℝ) ≤ 36 * Real.pi := by positivity
      nlinarith [hP'r]
    exact this
  have hsecond : Real.sqrt (((Q' : ℕ) : ℝ) ^ 3) ≤ Real.sqrt (((Q : ℝ)) ^ 3) := by
    refine Real.sqrt_le_sqrt ?_
    exact pow_le_pow_left₀ (Nat.cast_nonneg Q') hQ'r 3
  have hcoef : (0 : ℝ) ≤ 22 * Real.sqrt (36 * Real.pi / (T * |r / m₁ - r / m₂|)) := by
    positivity
  nlinarith [hfirst, hsecond, mul_le_mul_of_nonneg_left hsecond hcoef]

/-- **The off-diagonal correlation, sub-resonant regime.** -/
theorem norm_masked_correlation_offdiag_kuzminLandau_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B P Q : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P) {m₁ m₂ : ℕ}
    (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (hne : m₁ ≠ m₂)
    (h4₁ : 4 * (r / m₁) ≤ (P : ℝ)) (h4₂ : 4 * (r / m₂) ≤ (P : ℝ))
    (hsmall : T * |r / m₁ - r / m₂| / (2 * Real.pi * (P : ℝ) ^ 2) ≤ 1 / 2)
    (hY : 0 < T * |r / m₁ - r / m₂|) :
    ‖∑ d ∈ Finset.Ico P Q,
        maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖
      ≤ 75 * Real.pi * (Q : ℝ) ^ 2 / (16 * (T * |r / m₁ - r / m₂|)) + 1 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set P' : ℕ := max P (max ((A - 1) / m₁ + 1) ((A - 1) / m₂ + 1)) with hP'
  set Q' : ℕ := min Q (min ((B - 1) / m₁ + 1) ((B - 1) / m₂ + 1)) with hQ'
  have hPP' : P ≤ P' := le_max_left _ _
  have hQQ' : Q' ≤ Q := min_le_left _ _
  have hP'1 : 1 ≤ P' := le_trans hP hPP'
  have hP'r : (P : ℝ) ≤ (P' : ℝ) := by exact_mod_cast hPP'
  have hQ'r : (Q' : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQQ'
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  rw [sum_masked_correlation_eq hA hB hP T r hm₁ hm₂, ← hP', ← hQ']
  by_cases hlt : P' < Q'
  · have hsmall' : T * |r / m₁ - r / m₂| / (2 * Real.pi * ((P' : ℕ) : ℝ) ^ 2) ≤ 1 / 2 := by
      refine le_trans ?_ hsmall
      refine div_le_div_of_nonneg_left hY.le (by positivity) ?_
      have hsq : (P : ℝ) ^ 2 ≤ ((P' : ℕ) : ℝ) ^ 2 := by nlinarith [hP'r, hP0]
      nlinarith [hsq, hpi]
    have hmain := norm_sum_ndExp_corr_kuzminLandau_abs_le (B := Q') hT hr hm₁ hm₂ hne hP'1 hlt
      (le_trans h4₁ hP'r) (le_trans h4₂ hP'r) hsmall'
    refine hmain.trans ?_
    have hstep : 75 * Real.pi * ((Q' : ℕ) : ℝ) ^ 2 / (16 * (T * |r / m₁ - r / m₂|))
        ≤ 75 * Real.pi * (Q : ℝ) ^ 2 / (16 * (T * |r / m₁ - r / m₂|)) := by
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have hsq : ((Q' : ℕ) : ℝ) ^ 2 ≤ (Q : ℝ) ^ 2 := by
        nlinarith [hQ'r, Nat.cast_nonneg (α := ℝ) Q']
      nlinarith [hsq, hpi]
    linarith
  · have hempty : Finset.Ico P' Q' = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hempty, Finset.sum_empty, norm_zero]
    positivity

end

end RHTower.Sieve
