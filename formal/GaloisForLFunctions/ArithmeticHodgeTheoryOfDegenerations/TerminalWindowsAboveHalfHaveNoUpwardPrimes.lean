import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheUpwardPrimeWindowsCarryTheShellCorrection

/-!
# Terminal windows above one half have no upward prime row

When the first prime multiple lies beyond the horizon and its shell,
every actual upward window is empty. A terminal support separated from
one half has this property at every vanishing atomic width, uniformly
over all conductors.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory

/-- The actual upward row is zero if its first possible prime multiple lies above the
entire punctured shell. -/
theorem upwardModeRow_eq_zero_of_horizon_lt_two_mul
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc : 0 < c) {N n H : ℕ}
    (hH : 2 * c ≤ H) (hN : 2 * c ≤ N) (hn : 1 ≤ n)
    (hfar : N + H < 2 * n) (m : ℕ) :
    upwardModeRow φ c N m n = 0 := by
  rw [upwardModeRow_eq_sum_inner hφ hsupp hc hH hN hn]
  apply sum_eq_zero
  intro k _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  by_cases hk1 : k = 1
  · subst k
    simp
  have hk2 : 2 ≤ k := by omega
  have hkn : N + H < k * n := hfar.trans_le (Nat.mul_le_mul_right n hk2)
  have hz : upwardInner φ c N m H (k * n) = 0 := by
    unfold upwardInner
    apply sum_eq_zero
    intro j hj
    have hjH := (mem_Icc.mp hj).2
    have hup : ¬k * n + j ≤ N := by omega
    have hdown : ¬(j < k * n ∧ k * n - j ≤ N) := by omega
    simp only [if_neg hup, if_neg hdown, add_zero]
  rw [hz, mul_zero]

/-- A terminal weight supported strictly above one half annihilates the actual upward
prime row eventually, uniformly in the incoming conductor. -/
theorem eventually_terminal_upwardModeRow_eq_zero
    {φ F : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {δ : ℝ} (hδ : (1 / 2 : ℝ) < δ) (hzero : ∀ x, x ≤ δ → F x = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, ∀ n ∈ Icc 1 N,
      F ((n : ℝ) / N) * upwardModeRow φ (c N) N m n = 0 := by
  have hlim := (hcN.const_mul 2).add (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  simp only [mul_zero, zero_add] at hlim
  have hε : 0 < min (1 : ℝ) (2 * δ - 1) := lt_min one_pos (by linarith only [hδ])
  filter_upwards [eventually_ge_atTop 1, hlim.eventually (gt_mem_nhds hε)] with N hN hsmall
  intro m n hn
  by_cases hx : (n : ℝ) / N ≤ δ
  · rw [hzero _ hx, zero_mul]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 := hc N
  let H : ℕ := ⌈2 * c N⌉₊
  have hH : 2 * c N ≤ (H : ℝ) := Nat.le_ceil _
  have hHu : (H : ℝ) < 2 * c N + 1 := Nat.ceil_lt_add_one (by positivity)
  have hratio : (2 * c N + 1) / N < min (1 : ℝ) (2 * δ - 1) := by
    simpa only [add_div, mul_div_assoc] using hsmall
  have hcn : 2 * c N ≤ (N : ℝ) := by
    have he := (div_lt_iff₀ hN0).mp (hratio.trans_le (min_le_left _ _))
    linarith only [he]
  have hfarR : (N : ℝ) + H < 2 * n := by
    have he := (div_lt_iff₀ hN0).mp (hratio.trans_le (min_le_right _ _))
    have hnδ := (lt_div_iff₀ hN0).mp (lt_of_not_ge hx)
    nlinarith only [he, hnδ, hHu]
  have hfar : N + H < 2 * n := by exact_mod_cast hfarR
  rw [upwardModeRow_eq_zero_of_horizon_lt_two_mul hφ hsupp hc0 hH hcn
    (mem_Icc.mp hn).1 hfar m, mul_zero]

/-- Every terminal pairing supported above one half has an eventually zero upward component. -/
theorem eventually_terminal_upward_pairing_eq_zero
    {φ F : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {δ : ℝ} (hδ : (1 / 2 : ℝ) < δ) (hzero : ∀ x, x ≤ δ → F x = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ,
      (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n * upwardModeRow φ (c N) N m n) = 0 := by
  filter_upwards [eventually_terminal_upwardModeRow_eq_zero hφ hsupp hδ hzero hc hcN]
    with N hN m
  apply sum_eq_zero
  intro n hn
  rw [div_mul_eq_mul_div, hN m n hn, zero_div]

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.eventually_terminal_upwardModeRow_eq_zero
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.eventually_terminal_upward_pairing_eq_zero
