import GaloisForLFunctions.RHTower.WeilLogShiftRecoveryAdaptive

/-!
# Bounded recovery histories with divergent local moments

Even the injective recovery mesh admits uniformly bounded histories whose signed,
excess, and deficit moments all diverge. An adaptive antipodal policy forces every
weighted arithmetic term to have absolute value at least one half. The one-sided
moment divergence laws then exclude finite excess and deficit moments, since the
recovery cutoffs are cofinal. No assertion concerns intervening real cutoffs.
-/

open Filter Topology Zeta23 Real
open scoped BigOperators

noncomputable section

namespace RHTower

open WeilExcess

/-- Recovery samples reach arbitrarily large cutoffs. -/
theorem tendsto_weilLogShiftRecoveryCutoff :
    Tendsto weilLogShiftRecoveryCutoff atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt (exp (2 * b + log 2))
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  have hcast : (N : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (show N ≤ n + 1 by omega)
  have hlog := log_lt_log (exp_pos (2 * b + log 2)) (hN.trans_le hcast)
  rw [log_exp] at hlog
  dsimp only [weilLogShiftRecoveryCutoff]
  linarith only [hlog]

/-- The recovery diagonal is dominated by twice the paired full-kernel weight. -/
theorem weilLogShiftRecoveryWeight_diagonal_le (n : ℕ) (hn : 2 ≤ n) :
    weilLogShiftRecoveryWeight n n ≤ 2 * pairedLogKernel (log 2) n / sqrt n := by
  rw [weilLogShiftRecoveryWeight_diagonal n hn]
  apply div_le_div_of_nonneg_right _ (sqrt_nonneg _)
  have hK := truncatedRiemannAutocorr_le_riemannAutocorr
    (weilLogShiftRecoveryCutoff n) (log n - log 2)
  have heven : riemannAutocorr (log n - log 2) = riemannAutocorr (log 2 - log n) := by
    rw [show log n - log 2 = -(log 2 - log n) by ring, riemannAutocorr_neg]
  rw [heven] at hK
  have hnonneg := riemannAutocorr_nonneg (log 2 + log n)
  dsimp only [pairedLogKernel]
  linarith only [hK, hnonneg]

/-- Preserve any finite sample prefix, then choose antipodal targets. All later
samples have magnitude one and all later weighted terms have magnitude at least one half. -/
theorem exists_antipodal_recovery_after_prefix (height : ℕ → ℝ) (M : ℕ) :
    ∃ lam : ℕ → ℝ,
      (∀ k : ℕ, k < M → weilLogShiftRecoveryProbe lam (k + 2) = height k) ∧
      (∀ n : ℕ, M + 2 ≤ n → |weilLogShiftRecoveryProbe lam n| = 1) ∧
      (∀ n : ℕ, M + 2 ≤ n →
        (1 / 2 : ℝ) ≤ |weilDeviation lam n| * pairedLogKernel (log 2) n) := by
  let base : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n
  let target (k : ℕ) (state : ℕ → ℝ) : ℝ :=
    if k < M then height k else
      if weilLogShiftRecoveryProbe state (k + 2) ≤ 0 then 1 else -1
  let lam := weilLogShiftRecoveryAdaptive base target
  let stateAt (n : ℕ) := weilLogShiftRecoveryPrefix base lam n
  have hallprobe (k : ℕ) : weilLogShiftRecoveryProbe lam (k + 2) =
      if k < M then height k else
        if weilLogShiftRecoveryProbe (stateAt (k + 2)) (k + 2) ≤ 0 then 1 else -1 :=
    weilLogShiftRecoveryAdaptive_probe base target k
  have hprobe (n : ℕ) (hn : M + 2 ≤ n) :
      weilLogShiftRecoveryProbe lam n =
        if weilLogShiftRecoveryProbe (stateAt n) n ≤ 0 then 1 else -1 := by
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
    rw [hallprobe, if_neg (show ¬ k < M by omega)]
  refine ⟨lam, fun k hk => by rw [hallprobe, if_pos hk], ?_, ?_⟩
  · intro n htail
    rw [hprobe n htail]
    split_ifs <;> norm_num
  · intro n htail
    have hn : 2 ≤ n := by omega
    have hgap : 1 ≤ |weilLogShiftRecoveryProbe lam n -
        weilLogShiftRecoveryProbe (stateAt n) n| := by
      rw [hprobe n htail]
      split_ifs with hq
      · rw [abs_of_nonneg (by linarith only [hq])]
        linarith only [hq]
      · have hqpos : 0 < weilLogShiftRecoveryProbe (stateAt n) n := by linarith only [hq]
        rw [abs_of_nonpos (by linarith only [hqpos])]
        linarith only [hqpos]
    have hdiff := weilLogShiftRecoveryProbe_first_difference lam (stateAt n) n hn
      (fun j _ hj => by simp only [stateAt, weilLogShiftRecoveryPrefix, if_pos hj])
    have hbase : stateAt n n = (ArithmeticFunction.vonMangoldt n : ℝ) := by
      simp only [stateAt, weilLogShiftRecoveryPrefix, lt_self_iff_false, if_false, base]
    rw [hdiff, hbase, abs_mul,
      abs_of_pos (weilLogShiftRecoveryWeight_diagonal_pos n hn)] at hgap
    have hupper := mul_le_mul_of_nonneg_right
      (weilLogShiftRecoveryWeight_diagonal_le n hn)
      (abs_nonneg (lam n - (ArithmeticFunction.vonMangoldt n : ℝ)))
    have hdev : |weilDeviation lam n| =
        |lam n - (ArithmeticFunction.vonMangoldt n : ℝ)| / sqrt n := by
      simp only [weilDeviation, if_pos hn, abs_div, abs_of_nonneg (sqrt_nonneg _)]
    rw [hdev]
    have hterm : 1 ≤ 2 *
        (|lam n - (ArithmeticFunction.vonMangoldt n : ℝ)| / sqrt n *
          pairedLogKernel (log 2) n) := by
      calc
        1 ≤ weilLogShiftRecoveryWeight n n *
            |lam n - (ArithmeticFunction.vonMangoldt n : ℝ)| := hgap
        _ ≤ (2 * pairedLogKernel (log 2) n / sqrt n) *
            |lam n - (ArithmeticFunction.vonMangoldt n : ℝ)| := hupper
        _ = _ := by ring
    linarith only [hterm]

/-- Antipodal target choices keep all samples at ±1 while every weighted
arithmetic term has magnitude at least one half. -/
theorem exists_antipodal_recovery_with_large_terms :
    ∃ lam : ℕ → ℝ,
      (∀ n : ℕ, 2 ≤ n → |weilLogShiftRecoveryProbe lam n| = 1) ∧
      (∀ n : ℕ, 2 ≤ n →
        (1 / 2 : ℝ) ≤ |weilDeviation lam n| * pairedLogKernel (log 2) n) := by
  obtain ⟨lam, _, hprobe, hterm⟩ := exists_antipodal_recovery_after_prefix (fun _ => 0) 0
  exact ⟨lam, hprobe, hterm⟩

/-- On a bounded cofinal recovery mesh, failure of signed summability forces
failure of both one-sided local moments. -/
theorem nonsummable_excess_deficit_of_bounded_recovery (lam : ℕ → ℝ)
    (hbounded : ∀ n : ℕ, 2 ≤ n → |weilLogShiftRecoveryProbe lam n| ≤ 1)
    (hbad : ¬ Summable fun n => weilDeviation lam n * pairedLogKernel (log 2) n) :
    (¬ Summable fun n => deviationExcess lam n * pairedLogKernel (log 2) n) ∧
      (¬ Summable fun n => deviationDeficit lam n * pairedLogKernel (log 2) n) := by
  constructor
  · intro hexc
    have hlim := (tendsto_logShift_probe_atBot_of_nonsummable_sample_of_local_excess
      (m := 2) (by omega) hexc hbad).comp tendsto_weilLogShiftRecoveryCutoff
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_le_atBot (-2))
    have hlow := (neg_le_abs (weilLogShiftRecoveryProbe lam (N + 2))).trans
      (hbounded (N + 2) (by omega))
    have hsmall : weilLogShiftRecoveryProbe lam (N + 2) ≤ -2 := hN (N + 2) (by omega)
    linarith only [hlow, hsmall]
  · intro hdef
    have hlim := (tendsto_logShift_probe_atTop_of_nonsummable_sample_of_local_deficit
      (m := 2) (by omega) hdef hbad).comp tendsto_weilLogShiftRecoveryCutoff
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_ge_atTop 2)
    have hhigh := (le_abs_self (weilLogShiftRecoveryProbe lam (N + 2))).trans
      (hbounded (N + 2) (by omega))
    have hlarge : 2 ≤ weilLogShiftRecoveryProbe lam (N + 2) := hN (N + 2) (by omega)
    linarith only [hhigh, hlarge]

/-- Bounded data on the injective recovery mesh do not imply any of the three
local moment conditions: both one-sided moments and the signed series fail. -/
theorem exists_bounded_recovery_with_divergent_excess_and_deficit :
    ∃ lam : ℕ → ℝ,
      (∀ n : ℕ, 2 ≤ n → |weilLogShiftRecoveryProbe lam n| = 1) ∧
      (¬ Summable fun n => deviationExcess lam n * pairedLogKernel (log 2) n) ∧
      (¬ Summable fun n => deviationDeficit lam n * pairedLogKernel (log 2) n) ∧
      (¬ Summable fun n => weilDeviation lam n * pairedLogKernel (log 2) n) := by
  obtain ⟨lam, hbounded, hlarge⟩ := exists_antipodal_recovery_with_large_terms
  have hbad : ¬ Summable fun n => weilDeviation lam n * pairedLogKernel (log 2) n := by
    intro hs
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((tendsto_order.mp hs.norm.tendsto_atTop_zero).2 (1 / 2) (by norm_num))
    have hsmall := hN (N + 2) (by omega)
    simp only [Real.norm_eq_abs, abs_mul,
      abs_of_pos (pairedLogKernel_pos (log 2) (N + 2))] at hsmall
    exact (not_lt_of_ge (hlarge (N + 2) (by omega))) hsmall
  obtain ⟨hexc, hdef⟩ := nonsummable_excess_deficit_of_bounded_recovery lam
    (fun n hn => (hbounded n hn).le) hbad
  exact ⟨lam, hbounded, hexc, hdef, hbad⟩

end RHTower
