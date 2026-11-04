import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TerminalConductorSourcesAreSummableBelowOverlap

/-!
# Every terminal window admits an arithmetic collar cutoff

A receiver separated from zero has no prefix below its support and
uniformly bounded seventh collar mass. Twice the arithmetic prime
strip eventually lies below that support at every critical ratio.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticHodgeTheoryOfDegenerations RenormalizedArithmeticPotentialTheory

/-- Every cutoff below the terminal support has an exactly vanishing receiver prefix. -/
theorem terminal_window_prefix_eq_zero {h : ℝ → ℝ} {δ : ℝ}
    (hlow : ∀ x, x ≤ δ → logProfile h x = 0)
    {N M : ℕ} (hN : 1 ≤ N) (hMN : M ≤ N) (hM : (M : ℝ) ≤ δ * N) :
    (∑ n ∈ Icc 1 M,
      primeHorizonExtension (horizonProfileVector (horizonWeights h N) N) n ^ 2) = 0 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  apply sum_eq_zero
  intro n hn
  have hnN : n ∈ Icc 1 N := mem_Icc.mpr
    ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans hMN⟩
  have hx : (n : ℝ) / N ≤ δ := by
    apply (div_le_iff₀ hN0).mpr
    exact (Nat.cast_le.mpr (mem_Icc.mp hn).2).trans hM
  rw [horizonProfileVector_horizonWeights_eq_terminal h hN, primeHorizonExtension, dif_pos hnN]
  change (logProfile h ((n : ℝ) / N) / Real.sqrt n) ^ 2 = 0
  rw [hlow _ hx, zero_div, zero_pow two_ne_zero]

/-- Terminal support bounds every seventh collar mass, independently of its lower cutoff. -/
theorem topCollarSeventhMass_terminal_le {h : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ x, x ≤ δ → logProfile h x = 0) {N : ℕ} (hN : 1 ≤ N) (M : ℕ) :
    topCollarSeventhMass M N
        (primeHorizonExtension (horizonProfileVector (horizonWeights h N) N)) ≤
      (1 / δ) ^ 7 * ‖horizonProfileVector (horizonWeights h N) N‖ ^ 2 := by
  let x := horizonProfileVector (horizonWeights h N) N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsub : Ioc M N ⊆ Icc 1 N := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hn
    exact mem_Icc.mpr ⟨by omega, hhi⟩
  have hval (n : ℕ) (hn : n ∈ Icc 1 N) :
      primeHorizonExtension x n = logProfile h ((n : ℝ) / N) / Real.sqrt n := by
    dsimp only [x]
    rw [horizonProfileVector_horizonWeights_eq_terminal h hN, primeHorizonExtension, dif_pos hn]
    rfl
  have hpoint (n : ℕ) (hn : n ∈ Ioc M N) :
      ((N : ℝ) / n) ^ 7 * primeHorizonExtension x n ^ 2 ≤
        (1 / δ) ^ 7 * primeHorizonExtension x n ^ 2 := by
    rw [hval n (hsub hn)]
    by_cases hz : logProfile h ((n : ℝ) / N) = 0
    · simp only [hz, zero_div, zero_pow two_ne_zero, mul_zero, le_refl]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp (hsub hn)).1
    have hx : δ < (n : ℝ) / N := lt_of_not_ge fun hh => hz (hlow _ hh)
    have hratio : (N : ℝ) / n ≤ 1 / δ := by
      apply (div_le_div_iff₀ hn0 hδ).mpr
      simpa only [one_mul, mul_comm (N : ℝ) δ] using ((lt_div_iff₀ hN0).mp hx).le
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg N) hn0.le) hratio 7) (sq_nonneg _)
  change topCollarSeventhMass M N (primeHorizonExtension x) ≤ _
  unfold topCollarSeventhMass
  calc
    _ ≤ ∑ n ∈ Ioc M N, (1 / δ) ^ 7 * primeHorizonExtension x n ^ 2 := sum_le_sum hpoint
    _ = (1 / δ) ^ 7 * ∑ n ∈ Ioc M N, primeHorizonExtension x n ^ 2 := (mul_sum _ _ _).symm
    _ ≤ (1 / δ) ^ 7 * ∑ n ∈ Icc 1 N, primeHorizonExtension x n ^ 2 :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _) (by positivity)
    _ = _ := by rw [sum_primeHorizonExtension_sq]

/-- The arithmetic strip is eventually an admissible cutoff below any fixed terminal support. -/
theorem eventually_critical_terminal_collar_cutoff {δ : ℝ} (hδ : 0 < δ)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ N ∧ 2 * linearPrimeStrip (c N) ≤ N ∧
        ((2 * linearPrimeStrip (c N) : ℕ) : ℝ) ≤ δ * N := by
  have ht := (criticalCurve_pow_log_div_natCast hc hR hcrit 1 0).const_mul
    (2 * (Real.exp 1 + 1))
  simp only [pow_one, pow_zero, mul_one, mul_zero] at ht
  filter_upwards [eventually_critical_half_collar_admissible hc hR hcrit,
    ht.eventually (gt_mem_nhds hδ)] with N ha hs
  obtain ⟨hN, _, _, _, _, hstrip⟩ := ha
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsmall : 2 * (Real.exp 1 + 1) * c N ≤ δ * N := by
    apply (div_le_iff₀ hN0).mp
    simpa only [mul_div_assoc] using hs.le
  refine ⟨hN, hstrip.trans (Nat.div_le_self N 2), ?_⟩
  push_cast
  calc
    (2 : ℝ) * linearPrimeStrip (c N) ≤ 2 * ((Real.exp 1 + 1) * c N) :=
      mul_le_mul_of_nonneg_left (linearPrimeStrip_le (hc N)) (by norm_num)
    _ ≤ δ * N := by simpa only [mul_assoc] using hsmall

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.terminal_window_prefix_eq_zero
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.topCollarSeventhMass_terminal_le
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_critical_terminal_collar_cutoff
