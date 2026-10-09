import GaloisForLFunctions.RHTower.WeilLogShiftSmoothEdgeBound
import GaloisForLFunctions.RHTower.WeilLogShiftDiagonalObstruction

/-!
# Smooth recovery edges force origin diagonal divergence

The recovery diagonal loses exp(4−4n) at the cutoff edge. Since π<4, the
existing strict-rate bounds for the paired kernels imply positive exponential
growth of its origin inverse response. Every bounded finite history prefix
therefore admits a single extension with nonsummable signed moments at every
real shift. Such histories are dense, and the universal bounded-history moment
receiver fails at every shift. No claim about all histories or one-sided origin
moments is made.
-/

open Filter Topology Zeta23 Real
open scoped BigOperators BoundedContinuousFunction

noncomputable section

namespace RHTower

open WeilExcess

/-- Every rate strictly below 4−π is exceeded by an exponential lower
envelope for the origin inverse diagonal. -/
theorem exists_weilLogShiftOriginDiagonal_exponential_lower_above {σ : ℝ}
    (hσ : σ < 4 - π) :
    ∃ c γ : ℝ, 0 < c ∧ σ < γ ∧ ∀ᶠ k : ℕ in atTop,
      c * exp (γ * (k + 2 : ℕ)) ≤ weilLogShiftRecoveryMomentResponse 0 (k + 2) k := by
  have hgap : max 0 (σ + 2 * π - 4) < π :=
    max_lt_iff.mpr ⟨pi_pos, by linarith only [hσ]⟩
  obtain ⟨a, ha, hapi⟩ := exists_between hgap
  have ha0 : 0 < a := (le_max_left _ _).trans_lt ha
  have habgap : 2 * π < a + 4 - σ := by
    have h := (le_max_right _ _).trans_lt ha
    linarith only [h]
  obtain ⟨b, hb, hba⟩ := exists_between habgap
  have hrate2 : logKernelCriticalRate (log 2) = π := by
    have h := logKernelCriticalRate_log_nat (m := 2) (by omega)
    norm_num at h
    exact h
  have hrate0 : logKernelCriticalRate 0 = 2 * π := by simp [logKernelCriticalRate]
  obtain ⟨C, hC0, hC⟩ := exists_paired_logKernel_upper_of_lt_rate
    (y := log 2) ha0 (by rw [hrate2]; exact hapi)
  obtain ⟨D, hD0, hD⟩ := exists_paired_logKernel_lower_of_rate_lt
    (y := 0) (by rw [hrate0]; exact hb)
  let A : ℝ := 2 * C * exp 4
  let c : ℝ := D / A
  let γ : ℝ := a + 4 - b
  have hA : 0 < A := by dsimp only [A]; positivity
  have hc : 0 < c := div_pos hD0 hA
  have hγ : σ < γ := by dsimp only [γ]; linarith only [hba]
  have hden (n : ℕ) (hn : 2 ≤ n) :
      sqrt n * weilLogShiftRecoveryWeight n n ≤ A * exp (-((a + 4) * n)) := by
    have hkernel : pairedLogKernel (log 2) n ≤ C * exp (-(a * n)) := hC n (by omega)
    have he : exp (4 - 4 * n) * exp (-(a * n)) =
        exp 4 * exp (-((a + 4) * n)) := by
      rw [← exp_add, ← exp_add]
      congr 1
      ring
    calc
      _ ≤ 2 * exp (4 - 4 * n) * pairedLogKernel (log 2) n :=
        weilLogShiftRecoveryWeight_smooth_edge_bound n hn
      _ ≤ 2 * exp (4 - 4 * n) * (C * exp (-(a * n))) :=
        mul_le_mul_of_nonneg_left hkernel (by positivity)
      _ = (2 * C) * (exp (4 - 4 * n) * exp (-(a * n))) := by ring
      _ = A * exp (-((a + 4) * n)) := by rw [he]; dsimp only [A]; ring
  obtain ⟨N, hN⟩ := eventually_atTop.mp hD
  refine ⟨c, γ, hc, hγ, eventually_atTop.mpr ⟨N, fun k hk => ?_⟩⟩
  rw [weilLogShiftRecoveryMomentResponse_diagonal]
  let n : ℕ := k + 2
  have hn : 2 ≤ n := by dsimp only [n]; omega
  have hdenpos : 0 < sqrt n * weilLogShiftRecoveryWeight n n :=
    mul_pos (sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega)))
      (weilLogShiftRecoveryWeight_diagonal_pos n hn)
  change c * exp (γ * n) ≤ pairedLogKernel 0 n / (sqrt n * weilLogShiftRecoveryWeight n n)
  apply (le_div_iff₀ hdenpos).mpr
  have hcancel : c * exp (γ * n) * (A * exp (-((a + 4) * n))) =
      D * exp (-(b * n)) := by
    calc
      _ = (c * A) * (exp (γ * n) * exp (-((a + 4) * n))) := by ring
      _ = _ := by
        rw [show c * A = D from div_mul_cancel₀ D hA.ne', ← exp_add]
        congr 1
        congr 1
        dsimp only [γ]
        ring
  calc
    _ ≤ c * exp (γ * n) * (A * exp (-((a + 4) * n))) :=
      mul_le_mul_of_nonneg_left (hden n hn) (mul_pos hc (exp_pos _)).le
    _ = D * exp (-(b * n)) := hcancel
    _ ≤ pairedLogKernel 0 n := hN n (by dsimp only [n]; omega)

/-- The origin inverse diagonal has a positive exponential lower envelope.
The rate gap is supplied by π<4 and the actual smooth cutoff. -/
theorem exists_weilLogShiftOriginDiagonal_exponential_lower :
    ∃ c γ : ℝ, 0 < c ∧ 0 < γ ∧ ∀ᶠ k : ℕ in atTop,
      c * exp (γ * (k + 2 : ℕ)) ≤ weilLogShiftRecoveryMomentResponse 0 (k + 2) k :=
  exists_weilLogShiftOriginDiagonal_exponential_lower_above (by linarith only [pi_lt_four])

/-- Even the origin diagonal is nonsummable; there is no universally safe
interior shift on this recovery mesh. -/
theorem not_summable_weilLogShiftRecoveryDiagonal_origin :
    ¬ Summable (fun k => weilLogShiftRecoveryMomentResponse 0 (k + 2) k) := by
  intro hs
  obtain ⟨c, γ, hc, hγ, hlower⟩ := exists_weilLogShiftOriginDiagonal_exponential_lower
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlower
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    ((tendsto_order.mp hs.tendsto_atTop_zero).2 (c / 2) (by positivity))
  have hlow := hN (max N M) (le_max_left _ _)
  have hhigh := hM (max N M) (le_max_right _ _)
  have hex : 1 ≤ exp (γ * (max N M + 2 : ℕ)) := one_le_exp_iff.mpr (by positivity)
  nlinarith only [hlow, hhigh, hex, hc]

private theorem nowhere_summable_of_diagonal_obstruction
    {height : WeilLogShiftBoundedHistory} (hh : WeilLogShiftDiagonalObstruction height) :
    ∀ y : ℝ, ¬ Summable (weilLogShiftRecoveryMoment y (weilLogShiftBoundedHistoryValues height)) := by
  have hzero := hh 0 not_summable_weilLogShiftRecoveryDiagonal_origin
  intro y hs
  apply hzero
  change Summable (fun n => weilDeviation
    (weilLogShiftRecoveryInverse (weilLogShiftBoundedHistoryValues height)) n * pairedLogKernel 0 n)
  exact summable_kernelPotential_of_abs_le
    (by simpa only [abs_zero] using abs_nonneg y) hs

/-- Every bounded finite prefix extends to one bounded history with divergent
signed moments at every real shift, including the origin. -/
theorem exists_weilLogShiftBoundedHistory_prefix_nowhere_summable
    (height : WeilLogShiftBoundedHistory) (M : ℕ) :
    ∃ extended : WeilLogShiftBoundedHistory,
      (∀ k : ℕ, k < M → extended k = height k) ∧
      ∀ y : ℝ, ¬ Summable (weilLogShiftRecoveryMoment y (weilLogShiftBoundedHistoryValues extended)) := by
  obtain ⟨extended, hprefix, hbad⟩ :=
    exists_weilLogShiftBoundedHistory_prefix_diagonal_obstruction height M
  exact ⟨extended, hprefix, nowhere_summable_of_diagonal_obstruction hbad⟩

/-- Bounded histories with no summable signed moment at any shift are dense
in the unit product cube. -/
theorem dense_weilLogShiftBounded_nowhere_summable :
    Dense {height : WeilLogShiftBoundedHistory | ∀ y : ℝ,
      ¬ Summable (weilLogShiftRecoveryMoment y (weilLogShiftBoundedHistoryValues height))} :=
  dense_weilLogShiftDiagonalObstruction.mono
    (fun _ hh => nowhere_summable_of_diagonal_obstruction hh)

/-- No real shift has universal moment summability on the bounded recovery cube. -/
theorem not_weilLogShiftBoundedMomentSummable (y : ℝ) :
    ¬ WeilLogShiftBoundedMomentSummable y := by
  intro hs
  let zeroHistory : WeilLogShiftBoundedHistory := fun _ => ⟨0, by norm_num⟩
  obtain ⟨height, _, hbad⟩ :=
    exists_weilLogShiftBoundedHistory_prefix_nowhere_summable zeroHistory 0
  exact hbad y (hs height)

/-- The exact finite matrix receiver is unbounded at every real shift. -/
theorem unbounded_weilLogShiftRecoveryMatrixBudget (y C : ℝ) :
    ∃ (N : ℕ) (sign : Fin N → Bool), C < weilLogShiftRecoveryMatrixBudget y N sign := by
  by_contra h
  push Not at h
  apply not_weilLogShiftBoundedMomentSummable y
  apply (weilLogShiftBoundedMomentSummable_iff_matrix_bound y).mpr
  exact ⟨max C 0, le_max_right _ _, fun N sign => (h N sign).trans (le_max_left _ _)⟩

end RHTower
