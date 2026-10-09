import GaloisForLFunctions.RHTower.WeilFinitePanelPositiveCompletion

/-!
# Simultaneous positive completion of all tail log-shift panels

Positive coefficient changes beyond a window's probe-index block cannot lower
that window's panel. Successive one-coordinate completions therefore preserve
earlier bounds. Each coefficient becomes constant after finitely many steps,
giving a single sequence meeting arbitrary real height targets at every later
window while preserving the initial coefficient block.
-/

open Complex MeasureTheory Set Zeta23
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Exact real paired kernel of a log-shift difference. -/
theorem logShiftRiemannPair_eq (L c y : ℝ) :
    EF.weilTest (logShiftRiemannDifference L c) (logShiftRiemannDifference L c) y +
      EF.weilTest (logShiftRiemannDifference L c) (logShiftRiemannDifference L c) (-y) =
      ((4 * truncatedRiemannAutocorr L y - 2 * truncatedRiemannAutocorr L (y + c) -
        2 * truncatedRiemannAutocorr L (y - c) : ℝ) : ℂ) := by
  rw [weilTest_logShiftRiemannDifference, weilTest_logShiftRiemannDifference,
    truncatedRiemannAutocorr_neg L y,
    show -y + c = -(y - c) by ring, show -y - c = -(y + c) by ring,
    truncatedRiemannAutocorr_neg L (y - c), truncatedRiemannAutocorr_neg L (y + c)]
  push_cast
  ring

/-- Increasing coefficients beyond the probe-index block cannot decrease any panel entry. -/
theorem weilLogShiftWindowPanel_outer_mono (k : ℕ) (lam mu : ℕ → ℝ)
    (hle : ∀ n, lam n ≤ mu n)
    (hhead : ∀ n : ℕ, (n : ℝ) ≤ Real.exp (2 * (k : ℝ)) → lam n = mu n)
    (m : Finset.Icc 2 ⌊Real.exp (2 * (k : ℝ))⌋₊) :
    (weilLogShiftWindowPanel k lam m).re ≤ (weilLogShiftWindowPanel k mu m).re := by
  have hdiff := weilLogShiftWindowPanel_sub k mu lam m
  simp_rw [logShiftRiemannPair_eq] at hdiff
  have hre := congrArg Complex.re hdiff
  simp only [Complex.sub_re, Complex.neg_re, Complex.re_sum,
    ← Complex.ofReal_mul, Complex.ofReal_re] at hre
  have hsum : (∑ n ∈ Finset.Icc 2 ⌊Real.exp (4 * (k : ℝ))⌋₊,
      ((mu n - lam n) / Real.sqrt n) *
        (4 * truncatedRiemannAutocorr k (Real.log n) -
          2 * truncatedRiemannAutocorr k (Real.log n + Real.log m.1) -
          2 * truncatedRiemannAutocorr k (Real.log n - Real.log m.1))) ≤ 0 := by
    refine Finset.sum_nonpos fun n _ => ?_
    by_cases hn : (n : ℝ) ≤ Real.exp (2 * (k : ℝ))
    · rw [hhead n hn]
      simp only [sub_self, zero_div, zero_mul]
      exact le_rfl
    · have hy := Real.log_lt_log (Real.exp_pos _) (lt_of_not_ge hn)
      rw [Real.log_exp] at hy
      have hz : truncatedRiemannAutocorr k (Real.log n) = 0 :=
        truncatedRiemannAutocorr_eq_zero (hy.le.trans (le_abs_self _))
      rw [hz]
      refine mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (sub_nonneg.mpr (hle n)) (Real.sqrt_nonneg _)) ?_
      have h1 := truncatedRiemannAutocorr_nonneg k (Real.log n + Real.log m.1)
      have h2 := truncatedRiemannAutocorr_nonneg k (Real.log n - Real.log m.1)
      linarith only [h1, h2]
  linarith only [hre, hsum]

private def positiveStep (k : ℕ) (lam : ℕ → ℝ) (r : ℝ) : ℕ → ℝ :=
  fun n => lam n + if n = weilLogShiftLiftIndex k then
    Classical.choose (exists_weilLogShiftWindowPanel_positive_completion k lam r) else 0

private theorem positiveStep_spec (k : ℕ) (lam : ℕ → ℝ) (r : ℝ) :
    (∀ n, lam n ≤ positiveStep k lam r n) ∧
    (∀ n : ℕ, (n : ℝ) ≤ Real.exp (2 * ((k + 1 : ℕ) : ℝ)) →
      positiveStep k lam r n = lam n) ∧
    ∀ m, r < (weilLogShiftWindowPanel (k + 1) (positiveStep k lam r) m).re := by
  have h := Classical.choose_spec (exists_weilLogShiftWindowPanel_positive_completion k lam r)
  refine ⟨?_, h.2.1, h.2.2⟩
  intro n
  dsimp only [positiveStep]
  split_ifs <;> linarith only [h.1]

private def completionStages (base : ℕ) (lam : ℕ → ℝ) (height : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => lam
  | i + 1 => positiveStep (base + i) (completionStages base lam height i) (height (base + i + 1))

private theorem completionStages_mono (base : ℕ) (lam : ℕ → ℝ) (height : ℕ → ℝ) :
    Monotone (completionStages base lam height) := by
  apply monotone_nat_of_le_succ
  intro i n
  exact (positiveStep_spec (base + i) (completionStages base lam height i)
    (height (base + i + 1))).1 n

private theorem index_le_exp_window (base i : ℕ) :
    (i : ℝ) ≤ Real.exp (2 * ((base + i + 1 : ℕ) : ℝ)) := by
  have hi : (i : ℝ) ≤ ((base + i + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show i ≤ base + i + 1 by omega)
  have hx : 0 < 2 * ((base + i + 1 : ℕ) : ℝ) := by positivity
  have he := Real.add_one_lt_exp hx.ne'
  linarith only [hi, hx, he]

private theorem completionStages_head_eq (base : ℕ) (lam : ℕ → ℝ) (height : ℕ → ℝ)
    (i j n : ℕ) (hij : i ≤ j)
    (hn : (n : ℝ) ≤ Real.exp (2 * ((base + i + 1 : ℕ) : ℝ))) :
    completionStages base lam height j n = completionStages base lam height i n := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    have hb : Real.exp (2 * ((base + i + 1 : ℕ) : ℝ)) ≤
        Real.exp (2 * ((base + j + 1 : ℕ) : ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact_mod_cast (show 2 * (base + i + 1) ≤ 2 * (base + j + 1) by omega)
    exact ((positiveStep_spec (base + j) (completionStages base lam height j)
      (height (base + j + 1))).2.1 n (hn.trans hb)).trans ih

private def completionDiagonal (base : ℕ) (lam : ℕ → ℝ) (height : ℕ → ℝ) (n : ℕ) : ℝ :=
  completionStages base lam height n n

private theorem completionStages_le_diagonal (base : ℕ) (lam : ℕ → ℝ) (height : ℕ → ℝ)
    (i n : ℕ) : completionStages base lam height i n ≤ completionDiagonal base lam height n := by
  by_cases hi : i ≤ n
  · exact completionStages_mono base lam height hi n
  · have he := completionStages_head_eq base lam height n i n (by omega) (index_le_exp_window base n)
    change completionStages base lam height i n ≤ completionStages base lam height n n
    rw [he]

private theorem completionDiagonal_head_eq (base : ℕ) (lam : ℕ → ℝ) (height : ℕ → ℝ)
    (i n : ℕ) (hn : (n : ℝ) ≤ Real.exp (2 * ((base + i + 1 : ℕ) : ℝ))) :
    completionDiagonal base lam height n = completionStages base lam height i n := by
  change completionStages base lam height n n = completionStages base lam height i n
  by_cases hi : i ≤ n
  · exact completionStages_head_eq base lam height i n n hi hn
  · exact (completionStages_head_eq base lam height n i n (by omega)
      (index_le_exp_window base n)).symm

/-- One coefficient sequence meets arbitrary strict panel-height targets at every later
window, dominates the starting sequence, and preserves its entire initial index block. -/
theorem exists_weilLogShiftTail_positive_completion (base : ℕ) (lam : ℕ → ℝ) (height : ℕ → ℝ) :
    ∃ mu : ℕ → ℝ,
      (∀ n, lam n ≤ mu n) ∧
      (∀ n : ℕ, (n : ℝ) ≤ Real.exp (2 * ((base + 1 : ℕ) : ℝ)) → mu n = lam n) ∧
      ∀ k : ℕ, base + 1 ≤ k → ∀ m, height k < (weilLogShiftWindowPanel k mu m).re := by
  refine ⟨completionDiagonal base lam height, ?_, ?_, ?_⟩
  · intro n
    exact completionStages_le_diagonal base lam height 0 n
  · intro n hn
    exact completionDiagonal_head_eq base lam height 0 n (by simpa only [Nat.add_zero] using hn)
  · intro k hk m
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, k = base + i + 1 := ⟨k - (base + 1), by omega⟩
    have hpos : height (base + i + 1) < (weilLogShiftWindowPanel (base + i + 1)
        (completionStages base lam height (i + 1)) m).re :=
      (positiveStep_spec (base + i) (completionStages base lam height i)
        (height (base + i + 1))).2.2 m
    apply hpos.trans_le
    apply weilLogShiftWindowPanel_outer_mono _ _ _
      (completionStages_le_diagonal base lam height (i + 1)) ?_ m
    intro n hn
    exact (completionStages_head_eq base lam height i (i + 1) n (by omega) hn).trans
      (completionDiagonal_head_eq base lam height i n hn).symm

/-- The entire countable log-shift family admits positive completions of arbitrary
coefficients through exp(2), with no growth, summability or RH premise. -/
theorem exists_weilLogShiftTestsPositive_prescribed_head (lam : ℕ → ℝ) :
    ∃ mu : ℕ → ℝ, WeilLogShiftTestsPositive mu ∧
      (∀ n : ℕ, (n : ℝ) ≤ Real.exp 2 → mu n = lam n) ∧ (∀ n, lam n ≤ mu n) := by
  obtain ⟨mu, hle, hhead, hpanel⟩ := exists_weilLogShiftTail_positive_completion 0 lam (fun _ => 0)
  refine ⟨mu, ?_, ?_, hle⟩
  · intro k m hm2 hmE
    by_cases hk : k = 0
    · subst k
      norm_num at hmE
      omega
    · have hm : m ∈ Finset.Icc 2 ⌊Real.exp (2 * (k : ℝ))⌋₊ :=
        Finset.mem_Icc.mpr ⟨hm2, Nat.le_floor hmE⟩
      exact (hpanel k (by omega) ⟨m, hm⟩).le
  · intro n hn
    exact hhead n (by simpa using hn)

end RHTower

end
