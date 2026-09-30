import GaloisForLFunctions.RHTower.DQPTEtaDeriv
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteApproximation

/-!
# Exact arithmetic tails of the paired eta source

The installed finite eta sums retain the first `N` odd-even pairs. Their
literal omitted tail therefore starts at the odd endpoint `2 * N + 1`.
The installed DQPT antiderivative fences, telescoped over this shifted tail,
give the full-rate value and derivative bounds with their exact constants.

Both estimates apply throughout the positive half-plane with a positive
lower real-part bound and a norm ceiling. The central-box corollaries expose
the exact value and derivative errors used in finite arithmetic quotients.
Every complex pair is retained before taking the norm of the complete tail.
-/

open Complex Set RHTower RHTower.DQPT RiemannGaussian

namespace RHTower
noncomputable section

private theorem shifted_norm_tsum_le_neg_majorant (f : ℕ → ℂ) (G : ℝ → ℝ)
    (hmono : ∀ x y : ℝ, 1 ≤ x → x ≤ y → G x ≤ G y)
    (hnonpos : ∀ x : ℝ, 1 ≤ x → G x ≤ 0)
    (hterm : ∀ n : ℕ, ‖f n‖ ≤ G (2 * (n : ℝ) + 2) - G (2 * (n : ℝ) + 1))
    (N : ℕ) : ‖∑' n : ℕ, f (n + N)‖ ≤ -G (2 * (N : ℝ) + 1) := by
  let a : ℕ → ℝ := fun n => 2 * ((n + N : ℕ) : ℝ) + 1
  let b : ℕ → ℝ := fun n => 2 * ((n + N : ℕ) : ℝ) + 2
  have hb : ∀ n : ℕ, 1 ≤ b n := by
    intro n
    have hn := Nat.cast_nonneg (n + N) (α := ℝ)
    dsimp [b]
    linarith
  have hstep : ∀ n : ℕ, b n ≤ a (n + 1) := by
    intro n
    dsimp [a, b]
    push_cast
    linarith
  have hpartial : ∀ K : ℕ, ∑ n ∈ Finset.range K, ‖f (n + N)‖ ≤ -G (a 0) := by
    intro K
    have hcompare : ∑ n ∈ Finset.range K, ‖f (n + N)‖ ≤
        ∑ n ∈ Finset.range K, (G (b n) - G (a n)) :=
      Finset.sum_le_sum (fun n _ => hterm (n + N))
    have htel := dqpt_gap_telescope hmono hb hstep K
    have haK : 1 ≤ a K := by
      have hK := Nat.cast_nonneg (K + N) (α := ℝ)
      dsimp [a]
      linarith
    have hG := hnonpos (a K) haK
    linarith
  have hsum : Summable (fun n : ℕ => ‖f (n + N)‖) :=
    summable_of_sum_range_le (fun n => norm_nonneg _) hpartial
  calc
    ‖∑' n : ℕ, f (n + N)‖ ≤ ∑' n : ℕ, ‖f (n + N)‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ -G (a 0) := Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) hpartial
    _ = -G (2 * (N : ℝ) + 1) := by simp [a]

private theorem coreSummand_eq_etaTerm (s : ℂ) (n : ℕ) :
    pairedEtaCoreSummand s n = etaTerm s n := by
  simp [pairedEtaCoreSummand, etaTerm]

private theorem coreDerivativeSummand_eq_dqptEtaTermDeriv (s : ℂ) (n : ℕ) :
    pairedEtaCoreDerivativeSummand s n = dqptEtaTermDeriv s n := by
  have h := hasDerivAt_pairedEtaCoreSummand s n
  have hf : (fun w : ℂ => pairedEtaCoreSummand w n) = (fun w => etaTerm w n) := by
    funext w
    exact coreSummand_eq_etaTerm w n
  rw [hf] at h
  exact h.unique (hasDerivAt_etaTerm s n)

private theorem etaCore_norm_tail_le {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖pairedEtaCore s - pairedEtaCorePartialSum N s‖ ≤
      (‖s‖ / s.re) * (2 * (N : ℝ) + 1) ^ (-s.re) := by
  have heq : pairedEtaCore s - pairedEtaCorePartialSum N s =
      ∑' n : ℕ, pairedEtaCoreSummand s (n + N) := by
    change (∑' n : ℕ, pairedEtaCoreSummand s n) -
      (∑ n ∈ Finset.range N, pairedEtaCoreSummand s n) = _
    rw [← (summable_pairedEtaCoreSummand hs).sum_add_tsum_nat_add N]
    abel
  rw [heq]
  have h := shifted_norm_tsum_le_neg_majorant (pairedEtaCoreSummand s)
    (dqptEtaMajorant s) (dqptEtaMajorant_mono hs)
    (fun x hx => dqptEtaMajorant_nonpos hs (zero_lt_one.trans_le hx))
    (fun n => by
      rw [coreSummand_eq_etaTerm]
      exact norm_etaTerm_le_majorant hs n) N
  simpa [dqptEtaMajorant] using h

private theorem etaDerivative_norm_tail_le {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖pairedEtaArithmeticDerivativeValue s - pairedEtaCoreDerivativePartialSum N s‖ ≤
      (2 * (N : ℝ) + 1) ^ (-s.re) *
        (1 / s.re + ‖s‖ * (Real.log (2 * (N : ℝ) + 1) / s.re + 1 / s.re ^ 2)) := by
  have heq : pairedEtaArithmeticDerivativeValue s - pairedEtaCoreDerivativePartialSum N s =
      ∑' n : ℕ, pairedEtaCoreDerivativeSummand s (n + N) := by
    change (∑' n : ℕ, pairedEtaCoreDerivativeSummand s n) -
      (∑ n ∈ Finset.range N, pairedEtaCoreDerivativeSummand s n) = _
    rw [← (summable_pairedEtaCoreDerivativeSummand hs).sum_add_tsum_nat_add N]
    abel
  rw [heq]
  have h := shifted_norm_tsum_le_neg_majorant (pairedEtaCoreDerivativeSummand s)
    (dqptEtaDerivMajorant s) (dqptEtaDerivMajorant_mono hs)
    (fun x hx => dqptEtaDerivMajorant_nonpos hs hx)
    (fun n => by
      rw [coreDerivativeSummand_eq_dqptEtaTermDeriv]
      exact norm_dqptEtaTermDeriv_le_derivMajorant hs n) N
  convert h using 1
  dsimp [dqptEtaDerivMajorant]
  ring

/-- Exact value error after retaining precisely the first `N` eta pairs. -/
theorem liClockPairedEtaCore_sub_partialSum_norm_le {s : ℂ} {σ R : ℝ} (hσ : 0 < σ)
    (hσs : σ ≤ s.re) (hsR : ‖s‖ ≤ R) (N : ℕ) :
    ‖pairedEtaCore s - pairedEtaCorePartialSum N s‖ ≤
      (R / σ) * (2 * (N : ℝ) + 1) ^ (-σ) := by
  have hs : 0 < s.re := hσ.trans_le hσs
  have hR : 0 ≤ R := (norm_nonneg s).trans hsR
  have ha : 1 ≤ 2 * (N : ℝ) + 1 := by
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hpow : (2 * (N : ℝ) + 1) ^ (-s.re) ≤ (2 * (N : ℝ) + 1) ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le ha (by linarith)
  have hcoef : ‖s‖ / s.re ≤ R / σ :=
    (div_le_div_of_nonneg_left (norm_nonneg s) hσ hσs).trans
      (div_le_div_of_nonneg_right hsR hσ.le)
  exact (etaCore_norm_tail_le hs N).trans
    (mul_le_mul hcoef hpow (by positivity) (by positivity))

/-- Exact derivative error with the full exponential rate and logarithmic factor. -/
theorem liClockPairedEtaArithmeticDerivativeValue_sub_partialSum_norm_le
    {s : ℂ} {σ R : ℝ} (hσ : 0 < σ)
    (hσs : σ ≤ s.re) (hsR : ‖s‖ ≤ R) (N : ℕ) :
    ‖pairedEtaArithmeticDerivativeValue s - pairedEtaCoreDerivativePartialSum N s‖ ≤
      (2 * (N : ℝ) + 1) ^ (-σ) *
        (1 / σ + R * (Real.log (2 * (N : ℝ) + 1) / σ + 1 / σ ^ 2)) := by
  have hs : 0 < s.re := hσ.trans_le hσs
  have hR : 0 ≤ R := (norm_nonneg s).trans hsR
  have ha : 1 ≤ 2 * (N : ℝ) + 1 := by
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hlog : 0 ≤ Real.log (2 * (N : ℝ) + 1) := Real.log_nonneg ha
  have hpow : (2 * (N : ℝ) + 1) ^ (-s.re) ≤ (2 * (N : ℝ) + 1) ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le ha (by linarith)
  have h1 : 1 / s.re ≤ 1 / σ := one_div_le_one_div_of_le hσ hσs
  have hlogdiv : Real.log (2 * (N : ℝ) + 1) / s.re ≤
      Real.log (2 * (N : ℝ) + 1) / σ := div_le_div_of_nonneg_left hlog hσ hσs
  have hsq : σ ^ 2 ≤ s.re ^ 2 := by nlinarith
  have h2 : 1 / s.re ^ 2 ≤ 1 / σ ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hσ) hsq
  have hcoef : 1 / s.re + ‖s‖ *
        (Real.log (2 * (N : ℝ) + 1) / s.re + 1 / s.re ^ 2) ≤
      1 / σ + R * (Real.log (2 * (N : ℝ) + 1) / σ + 1 / σ ^ 2) :=
    add_le_add h1 (mul_le_mul hsR (add_le_add hlogdiv h2) (by positivity) hR)
  exact (etaDerivative_norm_tail_le hs N).trans
    (mul_le_mul hpow hcoef (by positivity) (by positivity))

/-- The value tail on the audited box has the exact envelope `3 * a ^ (-1/4)`. -/
theorem liClockPairedEtaCore_sub_partialSum_norm_le_on_central_box {s : ℂ}
    (hσ : (1 / 4 : ℝ) ≤ s.re) (hsR : ‖s‖ ≤ (3 / 4 : ℝ)) (N : ℕ) :
    ‖pairedEtaCore s - pairedEtaCorePartialSum N s‖ ≤
      3 * (2 * (N : ℝ) + 1) ^ (-(1 / 4 : ℝ)) := by
  convert liClockPairedEtaCore_sub_partialSum_norm_le (by norm_num) hσ hsR N using 1
  ring

/-- The derivative tail on the audited box has envelope `(16 + 3 log a) * a ^ (-1/4)`. -/
theorem liClockPairedEtaArithmeticDerivativeValue_sub_partialSum_norm_le_on_central_box
    {s : ℂ} (hσ : (1 / 4 : ℝ) ≤ s.re) (hsR : ‖s‖ ≤ (3 / 4 : ℝ)) (N : ℕ) :
    ‖pairedEtaArithmeticDerivativeValue s - pairedEtaCoreDerivativePartialSum N s‖ ≤
      (16 + 3 * Real.log (2 * (N : ℝ) + 1)) * (2 * (N : ℝ) + 1) ^ (-(1 / 4 : ℝ)) := by
  convert liClockPairedEtaArithmeticDerivativeValue_sub_partialSum_norm_le
    (by norm_num) hσ hsR N using 1
  ring

/-- The complete literal arithmetic derivative is bounded by `16` on the audited box. -/
theorem liClockPairedEtaArithmeticDerivativeValue_norm_le_sixteen_on_central_box
    {s : ℂ} (hσ : (1 / 4 : ℝ) ≤ s.re) (hsR : ‖s‖ ≤ (3 / 4 : ℝ)) :
    ‖pairedEtaArithmeticDerivativeValue s‖ ≤ (16 : ℝ) := by
  simpa [pairedEtaCoreDerivativePartialSum] using
    liClockPairedEtaArithmeticDerivativeValue_sub_partialSum_norm_le_on_central_box hσ hsR 0

end
end RHTower
