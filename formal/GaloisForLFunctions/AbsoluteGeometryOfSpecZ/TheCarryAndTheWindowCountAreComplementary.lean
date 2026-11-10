import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheCarryIsTheDefectOfTheWindowCount
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheGluingIndexCountsTheZeros

/-!
# The carry and the window count are complementary

`log binom(2N, N)` is the carry term of `N + N` plus the prime count of the window `(N, 2N]`. By
Stirling's formula the left side is `2N log 2 − ½ log(πN) + o(1)`: it has no arithmetic in it.

* **Complementarity** (`tendsto_carryDefect_add_windowDefect`): the defect of the carry term from
  its proportion `(2 log 2 − 1)N`, plus the defect of the window count from `N`, plus `½ log N`,
  tends to `−½ log π`.
* **A bound for one is a bound for the other** (`eventually_abs_carryDefect_le`,
  `eventually_abs_windowDefect_le`): if the defect of the window count is at most `E(N)`, the
  defect of the carry term from `(2 log 2 − 1)N − ½ log(πN)` is at most `E(N) + 1`, and
  conversely.

So the carry does not bound the defect of the window count by anything: up to `½ log(πN) + o(1)`
it is minus that defect. Transporting the count along the carry is an identity.
-/

open Filter Topology Real

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

theorem log_centralBinom_eq_log_factorial (N : ℕ) :
    Real.log ((Nat.centralBinom N : ℕ) : ℝ) =
      Real.log ((2 * N).factorial : ℝ) - 2 * Real.log (N.factorial : ℝ) := by
  have h : Nat.centralBinom N * (N.factorial * N.factorial) = (2 * N).factorial := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    have h1 := Nat.choose_mul_factorial_mul_factorial (show N ≤ 2 * N by omega)
    rw [show 2 * N - N = N by omega] at h1
    rw [← h1]
    ring
  have hc : (0 : ℝ) < Nat.centralBinom N := by exact_mod_cast Nat.centralBinom_pos N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  have h' : ((Nat.centralBinom N : ℕ) : ℝ) * ((N.factorial : ℝ) * N.factorial) =
      ((2 * N).factorial : ℝ) := by exact_mod_cast h
  rw [← h', Real.log_mul hc.ne' (by positivity), Real.log_mul hf.ne' hf.ne']
  ring

/-- Stirling's formula for the central binomial coefficient:
`log binom(2N, N) − 2N log 2 + ½ log N → −½ log π`. -/
theorem tendsto_log_centralBinom_sub :
    Tendsto (fun N : ℕ => Real.log ((Nat.centralBinom N : ℕ) : ℝ) - 2 * N * Real.log 2 +
      Real.log N / 2) atTop (𝓝 (-(Real.log π / 2))) := by
  have h := tendsto_log_factorial_sub_stirling
  have hdbl : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N two_pos) tendsto_id
  have hlim := (h.comp hdbl).sub (h.const_mul 2)
  have hval : Real.log π / 2 - 2 * (Real.log π / 2) = -(Real.log π / 2) := by ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e0 : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by
    push_cast
    ring
  have e2 : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log N :=
    Real.log_mul (by norm_num) hN0.ne'
  have e1 : Real.log (2 * (2 * (N : ℝ))) = Real.log 2 + (Real.log 2 + Real.log N) := by
    rw [Real.log_mul (by norm_num) (by positivity), e2]
  simp only [Function.comp_apply]
  rw [log_centralBinom_eq_log_factorial, e0, e1, e2]
  ring

/-- **The carry and the window count are complementary.** The defect of the carry term from
`(2 log 2 − 1)N` plus the defect of the window count from `N` is `−½ log(πN) + o(1)`. -/
theorem tendsto_carryDefect_add_windowDefect :
    Tendsto (fun N : ℕ => (carryTerm N - (2 * Real.log 2 - 1) * N) + (windowCount N - N) +
      Real.log N / 2) atTop (𝓝 (-(Real.log π / 2))) := by
  refine tendsto_log_centralBinom_sub.congr fun N => ?_
  rw [log_centralBinom_eq_carryTerm_add_window]
  ring

/-- A bound for the defect of the window count bounds the defect of the carry term from
`(2 log 2 − 1)N − ½ log(πN)`. -/
theorem eventually_abs_carryDefect_le {E : ℕ → ℝ}
    (h : ∀ᶠ N : ℕ in atTop, |windowCount N - N| ≤ E N) :
    ∀ᶠ N : ℕ in atTop,
      |carryTerm N - (2 * Real.log 2 - 1) * N + Real.log N / 2 + Real.log π / 2| ≤ E N + 1 := by
  have hev := tendsto_carryDefect_add_windowDefect.eventually (Metric.ball_mem_nhds _ one_pos)
  filter_upwards [h, hev] with N hN hb
  rw [Real.dist_eq, abs_lt] at hb
  rw [abs_le] at hN ⊢
  constructor <;> linarith [hb.1, hb.2, hN.1, hN.2]

/-- A bound for the defect of the carry term from `(2 log 2 − 1)N − ½ log(πN)` bounds the defect
of the window count. -/
theorem eventually_abs_windowDefect_le {E : ℕ → ℝ}
    (h : ∀ᶠ N : ℕ in atTop,
      |carryTerm N - (2 * Real.log 2 - 1) * N + Real.log N / 2 + Real.log π / 2| ≤ E N) :
    ∀ᶠ N : ℕ in atTop, |windowCount N - N| ≤ E N + 1 := by
  have hev := tendsto_carryDefect_add_windowDefect.eventually (Metric.ball_mem_nhds _ one_pos)
  filter_upwards [h, hev] with N hN hb
  rw [Real.dist_eq, abs_lt] at hb
  rw [abs_le] at hN ⊢
  constructor <;> linarith [hb.1, hb.2, hN.1, hN.2]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
