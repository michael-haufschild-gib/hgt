import GaloisForLFunctions.RHTower.WeilLogShiftFirstProbeInterpolation

/-!
# Exact coefficient reconstruction from the first probe

At cutoff `(log (n+1) - log 2)/2`, the m=2 probe sees precisely the arithmetic
head through n, with a strictly positive coefficient on its newest atom.
Its finite triangular difference formula reconstructs every coefficient at
n>=2 without growth or convergence assumptions. This fine mesh, and hence
the full positive-real-cutoff history, is injective modulo the two invisible
coordinates. Integer-cutoff histories can agree while these mesh values differ.
-/

open Filter Topology Zeta23 Real
open scoped BigOperators

noncomputable section

namespace RHTower

open WeilExcess

/-- The next atom's support boundary exposes the complete head through n. -/
def weilLogShiftRecoveryCutoff (n : ℕ) : ℝ := (log (n + 1 : ℕ) - log 2) / 2

/-- The first log-shift probe sampled at its coefficient-recovery cutoff. -/
def weilLogShiftRecoveryProbe (lam : ℕ → ℝ) (n : ℕ) : ℝ :=
  (weilFullFunctional lam (EF.weilTest
    (logShiftRiemannDifference (weilLogShiftRecoveryCutoff n) (log 2))
    (logShiftRiemannDifference (weilLogShiftRecoveryCutoff n) (log 2)))).re

/-- The real coefficient matrix of the recovery samples. -/
def weilLogShiftRecoveryWeight (n j : ℕ) : ℝ :=
  (2 * truncatedRiemannAutocorr (weilLogShiftRecoveryCutoff n) (log j + log 2) +
    2 * truncatedRiemannAutocorr (weilLogShiftRecoveryCutoff n) (log j - log 2) -
    4 * truncatedRiemannAutocorr (weilLogShiftRecoveryCutoff n) (log j)) / sqrt j

theorem weilLogShiftRecoveryCutoff_bounds (n : ℕ) (hn : 2 ≤ n) :
    0 < weilLogShiftRecoveryCutoff n ∧
    log n - log 2 < 2 * weilLogShiftRecoveryCutoff n ∧
    2 * weilLogShiftRecoveryCutoff n ≤ log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htwo : log (2 : ℝ) < log (n + 1 : ℕ) :=
    log_lt_log (by norm_num) (by exact_mod_cast (show 2 < n + 1 by omega))
  have hsucc : log (n : ℝ) < log (n + 1 : ℕ) :=
    log_lt_log hn0 (by exact_mod_cast (show n < n + 1 by omega))
  have hupper : log (n + 1 : ℕ) ≤ log (n : ℝ) + log 2 := by
    rw [← log_mul hn0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    apply log_le_log (by positivity)
    have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    nlinarith only [hnr]
  dsimp only [weilLogShiftRecoveryCutoff]
  constructor
  · linarith only [htwo]
  constructor <;> linarith only [hsucc, hupper]

private theorem recoveryAutocorr_tail (n j : ℕ) (hj : n < j) :
    truncatedRiemannAutocorr (weilLogShiftRecoveryCutoff n) (log j) = 0 ∧
    truncatedRiemannAutocorr (weilLogShiftRecoveryCutoff n) (log j + log 2) = 0 ∧
    truncatedRiemannAutocorr (weilLogShiftRecoveryCutoff n) (log j - log 2) = 0 := by
  have hlog : log (n + 1 : ℕ) ≤ log (j : ℝ) :=
    log_le_log (by positivity) (by exact_mod_cast (show n + 1 ≤ j by omega))
  have hc : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
  have hlo : 2 * weilLogShiftRecoveryCutoff n ≤ log j - log 2 := by
    dsimp only [weilLogShiftRecoveryCutoff]
    linarith only [hlog]
  refine ⟨truncatedRiemannAutocorr_eq_zero ?_,
    truncatedRiemannAutocorr_eq_zero ?_, truncatedRiemannAutocorr_eq_zero ?_⟩
  · exact (by linarith only [hlo, hc] : 2 * weilLogShiftRecoveryCutoff n ≤ log j).trans
      (le_abs_self _)
  · exact (by linarith only [hlo, hc] :
      2 * weilLogShiftRecoveryCutoff n ≤ log j + log 2).trans (le_abs_self _)
  · exact hlo.trans (le_abs_self _)

/-- No recovery sample depends on a coefficient beyond its indexed head. -/
theorem weilLogShiftRecoveryWeight_eq_zero_of_lt (n j : ℕ) (hj : n < j) :
    weilLogShiftRecoveryWeight n j = 0 := by
  obtain ⟨h0, hplus, hminus⟩ := recoveryAutocorr_tail n j hj
  simp only [weilLogShiftRecoveryWeight, h0, hplus, hminus, mul_zero, add_zero, sub_zero,
    zero_div]

/-- The newest atom has an explicit nonzero, positive response. -/
theorem weilLogShiftRecoveryWeight_diagonal (n : ℕ) (hn : 2 ≤ n) :
    weilLogShiftRecoveryWeight n n =
      2 * truncatedRiemannAutocorr (weilLogShiftRecoveryCutoff n) (log n - log 2) / sqrt n := by
  have hb := weilLogShiftRecoveryCutoff_bounds n hn
  have hc : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
  have h0 : truncatedRiemannAutocorr (weilLogShiftRecoveryCutoff n) (log n) = 0 :=
    truncatedRiemannAutocorr_eq_zero (hb.2.2.trans (le_abs_self _))
  have hplus : truncatedRiemannAutocorr (weilLogShiftRecoveryCutoff n) (log n + log 2) = 0 :=
    truncatedRiemannAutocorr_eq_zero
      ((by linarith only [hb.2.2, hc] : 2 * weilLogShiftRecoveryCutoff n ≤ log n + log 2).trans
        (le_abs_self _))
  simp only [weilLogShiftRecoveryWeight, h0, hplus, mul_zero, zero_add, sub_zero]

theorem weilLogShiftRecoveryWeight_diagonal_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < weilLogShiftRecoveryWeight n n := by
  rw [weilLogShiftRecoveryWeight_diagonal n hn]
  have hlog : log (2 : ℝ) ≤ log (n : ℝ) :=
    log_le_log (by norm_num) (by exact_mod_cast hn)
  have hK : 0 < truncatedRiemannAutocorr (weilLogShiftRecoveryCutoff n) (log n - log 2) := by
    apply (truncatedRiemannAutocorr_pos_iff _ _).mpr
    rw [abs_of_nonneg (sub_nonneg.mpr hlog)]
    exact (weilLogShiftRecoveryCutoff_bounds n hn).2.1
  exact div_pos (mul_pos (by norm_num) hK)
    (sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega)))

/-- Exact finite triangular response for arbitrary coefficient systems. Compact
support supplies every summability obligation; no full potential is assumed. -/
theorem weilLogShiftRecoveryProbe_sub (lam mu : ℕ → ℝ) (n : ℕ) :
    weilLogShiftRecoveryProbe lam n - weilLogShiftRecoveryProbe mu n =
      ∑ j ∈ Finset.Icc 2 n, (lam j - mu j) * weilLogShiftRecoveryWeight n j := by
  let L := weilLogShiftRecoveryCutoff n
  let f := logShiftRiemannDifference L (log 2)
  let g := EF.weilTest f f
  let term (v : ℕ → ℝ) (j : ℕ) : ℂ :=
    ((if 2 ≤ j then v j / sqrt j else 0 : ℝ) : ℂ) * (g (log j) + g (-log j))
  have hfc : HasCompactSupport f := hasCompactSupport_logShiftRiemannDifference _ _
  have hgc : HasCompactSupport g := EF.weilTest_hasCompactSupport hfc hfc
  have hs (v : ℕ → ℝ) : Summable (term v) :=
    summable_primeAtoms (fun j => if 2 ≤ j then v j / sqrt j else 0) hgc
  have hout (j : ℕ) (hj : j ∉ Finset.Icc 2 n) : term mu j - term lam j = 0 := by
    by_cases hj2 : 2 ≤ j
    · have hnj : n < j := by
        by_contra h
        exact hj (Finset.mem_Icc.mpr ⟨hj2, by omega⟩)
      obtain ⟨h0, hplus, hminus⟩ := recoveryAutocorr_tail n j hnj
      have hpair : g (log j) + g (-log j) = 0 := by
        change EF.weilTest (logShiftRiemannDifference L (log 2))
            (logShiftRiemannDifference L (log 2)) (log j) +
          EF.weilTest (logShiftRiemannDifference L (log 2))
            (logShiftRiemannDifference L (log 2)) (-log j) = 0
        rw [logShiftRiemannPair_eq]
        change ((4 * truncatedRiemannAutocorr (weilLogShiftRecoveryCutoff n) (log j) -
          2 * truncatedRiemannAutocorr (weilLogShiftRecoveryCutoff n) (log j + log 2) -
          2 * truncatedRiemannAutocorr (weilLogShiftRecoveryCutoff n) (log j - log 2) : ℝ) : ℂ) = 0
        simp only [h0, hplus, hminus, mul_zero, sub_self, Complex.ofReal_zero]
      simp only [term, hpair, mul_zero, sub_self]
    · simp only [term, if_neg hj2, Complex.ofReal_zero, zero_mul, sub_self]
  have hdiff : (∑' j, term mu j) - ∑' j, term lam j =
      ∑ j ∈ Finset.Icc 2 n, (((lam j - mu j) * weilLogShiftRecoveryWeight n j : ℝ) : ℂ) := by
    rw [← (hs mu).tsum_sub (hs lam), tsum_eq_sum hout]
    apply Finset.sum_congr rfl
    intro j hj
    have hj2 := (Finset.mem_Icc.mp hj).1
    dsimp only [term]
    simp only [if_pos hj2]
    change (((mu j / sqrt j : ℝ) : ℂ) *
      (EF.weilTest (logShiftRiemannDifference L (log 2))
          (logShiftRiemannDifference L (log 2)) (log j) +
        EF.weilTest (logShiftRiemannDifference L (log 2))
          (logShiftRiemannDifference L (log 2)) (-log j))) -
      (((lam j / sqrt j : ℝ) : ℂ) *
      (EF.weilTest (logShiftRiemannDifference L (log 2))
          (logShiftRiemannDifference L (log 2)) (log j) +
        EF.weilTest (logShiftRiemannDifference L (log 2))
          (logShiftRiemannDifference L (log 2)) (-log j))) = _
    simp only [logShiftRiemannPair_eq]
    dsimp only [weilLogShiftRecoveryWeight, L]
    push_cast
    ring
  have hcomplex : weilFullFunctional lam g - weilFullFunctional mu g =
      ∑ j ∈ Finset.Icc 2 n, (((lam j - mu j) * weilLogShiftRecoveryWeight n j : ℝ) : ℂ) := by
    unfold weilFullFunctional
    calc _ = (∑' j, term mu j) - ∑' j, term lam j := by dsimp only [term]; ring
      _ = _ := hdiff
  have hre := congrArg Complex.re hcomplex
  simpa only [weilLogShiftRecoveryProbe, g, f, L, Complex.sub_re, Complex.re_sum,
    Complex.ofReal_re] using hre

/-- Once the earlier coefficients agree, one more sample reads exactly the
next coefficient difference through a strictly positive scalar. -/
theorem weilLogShiftRecoveryProbe_first_difference (lam mu : ℕ → ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hhead : ∀ j : ℕ, 2 ≤ j → j < n → lam j = mu j) :
    weilLogShiftRecoveryProbe lam n - weilLogShiftRecoveryProbe mu n =
      weilLogShiftRecoveryWeight n n * (lam n - mu n) := by
  rw [weilLogShiftRecoveryProbe_sub lam mu n]
  rw [Finset.sum_eq_single n]
  · ring
  · intro j hj hjn
    have hmem := Finset.mem_Icc.mp hj
    rw [hhead j hmem.1 (by omega), sub_self, zero_mul]
  · intro hnot
    exact False.elim (hnot (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩))

/-- Equality of recovery samples through any finite index is exactly equality
of the corresponding coefficient head. -/
theorem weilLogShiftRecoveryProbe_prefix_iff (lam mu : ℕ → ℝ) (N : ℕ) :
    (∀ n : ℕ, 2 ≤ n → n ≤ N → weilLogShiftRecoveryProbe lam n = weilLogShiftRecoveryProbe mu n) ↔
      ∀ n : ℕ, 2 ≤ n → n ≤ N → lam n = mu n := by
  constructor
  · intro h n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn hN
      have hhead (j : ℕ) (hj : 2 ≤ j) (hjn : j < n) : lam j = mu j :=
        ih j hjn hj (hjn.le.trans hN)
      have hd := weilLogShiftRecoveryProbe_first_difference lam mu n hn hhead
      rw [h n hn hN, sub_self] at hd
      have hw := weilLogShiftRecoveryWeight_diagonal_pos n hn
      have heq : lam n - mu n = 0 := (mul_eq_zero.mp hd.symm).resolve_left hw.ne'
      exact sub_eq_zero.mp heq
  · intro h n _ hN
    apply sub_eq_zero.mp
    rw [weilLogShiftRecoveryProbe_sub lam mu n]
    apply Finset.sum_eq_zero
    intro j hj
    have hmem := Finset.mem_Icc.mp hj
    rw [h j hmem.1 (hmem.2.trans hN), sub_self, zero_mul]

/-- A countable mesh of m=2 samples determines all visible arithmetic
coefficients, with no growth, summability, sign, or RH hypothesis. -/
theorem weilLogShiftRecoveryProbe_eq_iff (lam mu : ℕ → ℝ) :
    (∀ n : ℕ, 2 ≤ n → weilLogShiftRecoveryProbe lam n = weilLogShiftRecoveryProbe mu n) ↔
      ∀ n : ℕ, 2 ≤ n → lam n = mu n := by
  constructor
  · intro h n hn
    exact (weilLogShiftRecoveryProbe_prefix_iff lam mu n).mp
      (fun j hj _ => h j hj) n hn le_rfl
  · intro h n hn
    exact (weilLogShiftRecoveryProbe_prefix_iff lam mu n).mpr
      (fun j hj _ => h j hj) n hn le_rfl

/-- The full positive-real-cutoff first-probe history is injective modulo
the forced invisible coefficients at zero and one. -/
theorem real_cutoff_firstProbe_eq_iff (lam mu : ℕ → ℝ) :
    (∀ L : ℝ, 0 < L →
      (weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference L (log 2)) (logShiftRiemannDifference L (log 2)))).re =
      (weilFullFunctional mu (EF.weilTest
        (logShiftRiemannDifference L (log 2)) (logShiftRiemannDifference L (log 2)))).re) ↔
      ∀ n : ℕ, 2 ≤ n → lam n = mu n := by
  constructor
  · intro h
    apply (weilLogShiftRecoveryProbe_eq_iff lam mu).mp
    intro n hn
    exact h (weilLogShiftRecoveryCutoff n) (weilLogShiftRecoveryCutoff_bounds n hn).1
  · intro h L _
    exact congrArg Complex.re (weilFullFunctional_congr h _)

/-- Integer-cutoff histories can coincide while a recovery-mesh sample
distinguishes the same coefficient systems. -/
theorem exists_integer_firstProbe_collision_detected_by_recovery_mesh :
    ∃ lam mu : ℕ → ℝ,
      (∀ k : ℕ, weilLogShiftFirstProbe lam k = weilLogShiftFirstProbe mu k) ∧
      ∃ n : ℕ, 2 ≤ n ∧ weilLogShiftRecoveryProbe lam n ≠ weilLogShiftRecoveryProbe mu n := by
  let mu : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ)
  obtain ⟨lam, hhistory, _, hbad⟩ :=
    exists_weilLogShiftFirstProbe_history_nonsummable (weilLogShiftFirstProbe mu)
  have hnot : ¬ ∀ n : ℕ, 2 ≤ n →
      weilLogShiftRecoveryProbe lam n = weilLogShiftRecoveryProbe mu n := by
    intro h
    have hcoef := (weilLogShiftRecoveryProbe_eq_iff lam mu).mp h
    have hdev (n : ℕ) : weilDeviation lam n = 0 := by
      by_cases hn : 2 ≤ n
      · simp only [weilDeviation, if_pos hn, hcoef n hn, mu, sub_self, zero_div]
      · simp only [weilDeviation, if_neg hn]
    apply hbad
    simpa only [hdev, zero_mul] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  push Not at hnot
  exact ⟨lam, mu, hhistory, hnot⟩

end RHTower
