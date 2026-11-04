import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.NearGammaDownwardCancellationHasPolynomialGrowth

/-!
# Interior terminal windows receive no exterior prime products

The exterior downward source occupies a strip of width proportional to
the overlap. A terminal profile separated from the horizon annihilates
that source eventually, uniformly over the incoming conductor.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
open SpacingScaleHarmonicAnalysis

/-- A terminal profile separated from one annihilates every exterior downward row
once the atomic width is sufficiently small. -/
theorem eventually_terminal_exteriorDownwardRow_eq_zero
    {φ F : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {η : ℝ} (hη : η < 1) (hzero : ∀ x, η ≤ x → F x = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, ∀ n ∈ Icc 1 N,
      F ((n : ℝ) / N) *
        actualExteriorDownwardRow (atomDilate φ (c N / N)) N m n = 0 := by
  have hlim := hcN.const_mul (Real.exp 1 + 1)
  simp only [mul_zero] at hlim
  filter_upwards [eventually_ge_atTop 1,
    hcN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hlim.eventually (gt_mem_nhds (sub_pos.mpr hη))] with N hN hw hsmall
  intro m n hn
  by_cases hx : η ≤ (n : ℝ) / N
  · rw [hzero _ hx, zero_mul]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hwidth : 0 < c N / N := div_pos hc0 hN0
  obtain ⟨_, hgsupp, _⟩ := atomDilate_facts hφ hsupp hwidth
  have hstrip := linearPrimeStrip_le (hc N)
  have hsmall' : (Real.exp 1 + 1) * c N < (1 - η) * N := by
    apply (div_lt_iff₀ hN0).mp
    simpa only [mul_div_assoc] using hsmall
  have hnη : (n : ℝ) < η * N := (div_lt_iff₀ hN0).mp (lt_of_not_ge hx)
  have hfarR : (n : ℝ) + linearPrimeStrip (c N) < N := by
    nlinarith only [hstrip, hsmall', hnη]
  have hfar : n < N - linearPrimeStrip (c N) := by
    have hnat : n + linearPrimeStrip (c N) < N := by exact_mod_cast hfarR
    omega
  have hz : actualExteriorDownwardRow (atomDilate φ (c N / N)) N m n = 0 := by
    rw [actualExteriorDownwardRow, downwardRamanujanRow_sub_interior_eq hc0 hn hgsupp m]
    exact regroupedExteriorDownwardPrimeRow_eq_zero_small_width hc0 hn hgsupp hw.le hfar m
  rw [hz, mul_zero]

/-- The full exterior pairing vanishes for every conductor at one common eventual horizon. -/
theorem eventually_terminal_exteriorDownward_pairing_eq_zero
    {φ F : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {η : ℝ} (hη : η < 1) (hzero : ∀ x, η ≤ x → F x = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ,
      (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / Real.sqrt n *
        actualExteriorDownwardRow (atomDilate φ (c N / N)) N m n) = 0 := by
  filter_upwards [eventually_terminal_exteriorDownwardRow_eq_zero hφ hsupp hη hzero hc hcN]
    with N hN m
  apply sum_eq_zero
  intro n hn
  rw [div_mul_eq_mul_div, hN m n hn, zero_div]

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.eventually_terminal_exteriorDownwardRow_eq_zero
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.eventually_terminal_exteriorDownward_pairing_eq_zero
