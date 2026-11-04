import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalUpwardShellsHaveTheirPolarMean
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiMobiusDivisorDilationChannels

/-!
# Terminal prime means are finite Riemann sums

The support of a terminal receiver bounds every prime multiplier before
the horizon limit. Exchanging the finite hyperbola sums therefore leaves
ordinary truncated Riemann sums, with a uniform one-cell error.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- The finite prime-power source read by a terminal receiver. -/
def finitePrimeTerminalMean (F : ℝ → ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 K, (Λ k : ℝ) * ∫ x in (0 : ℝ)..1 / k, F x

/-- Terminal support makes the multiplier cutoff independent of the horizon. -/
theorem sum_terminal_hyperbola_eq_finite
    {F : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hzero : ∀ x, x ≤ δ → F x = 0)
    {N K : ℕ} (hN : 1 ≤ N) (hKN : K ≤ N) (hK : 1 / δ ≤ K) (W : ℕ → ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, ∑ k ∈ Icc 1 (N / n), F ((n : ℝ) / N) * W n k) =
      ∑ k ∈ Icc 1 K, ∑ n ∈ Icc 1 (N / k), F ((n : ℝ) / N) * W n k := by
  rw [_root_.RHTower.sum_hyperbola_swap_real]
  symm
  apply sum_subset
  · intro k hk
    exact mem_Icc.mpr ⟨(mem_Icc.mp hk).1, (mem_Icc.mp hk).2.trans hKN⟩
  · intro k hk hkK
    have hk1 := (mem_Icc.mp hk).1
    have hklarge : K < k := by
      have hh : ¬(1 ≤ k ∧ k ≤ K) := by simpa only [mem_Icc] using hkK
      omega
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hkδ : 1 / (k : ℝ) ≤ δ := by
      apply (div_le_iff₀ hk0).mpr
      have hKk : (K : ℝ) ≤ k := by exact_mod_cast hklarge.le
      have hh := (div_le_iff₀ hδ).mp (hK.trans hKk)
      simpa only [mul_comm δ (k : ℝ)] using hh
    apply sum_eq_zero
    intro n hn
    have hnN := (Nat.le_div_iff_mul_le (show 0 < k from hk1)).mp (mem_Icc.mp hn).2
    have hx : (n : ℝ) / N ≤ 1 / k := by
      apply (div_le_div_iff₀ hN0 hk0).mpr
      simpa only [one_mul] using (show (n : ℝ) * k ≤ N by exact_mod_cast hnN)
    rw [hzero _ (hx.trans hkδ), zero_mul]

/-- The finite prime source has the sum of its uniform truncated Riemann errors. -/
theorem abs_finitePrime_riemannSum_sub_mean_le
    {F : ℝ → ℝ} {B L : ℝ} (hF : ∀ x, |F x| ≤ B) (hL : 0 ≤ L)
    (hFL : ∀ x y, |F x - F y| ≤ L * |x - y|)
    {N : ℕ} (hN : 1 ≤ N) (K : ℕ) :
    |(∑ k ∈ Icc 1 K, (Λ k : ℝ) * ((∑ n ∈ Icc 1 (N / k), F ((n : ℝ) / N)) / N)) -
      finitePrimeTerminalMean F K| ≤
      ((L + B) / N) * ∑ k ∈ Icc 1 K, (Λ k : ℝ) := by
  rw [finitePrimeTerminalMean, ← sum_sub_distrib, mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro k hk
  rw [← mul_sub, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact (mul_le_mul_of_nonneg_left
    (abs_terminal_truncated_riemannSum_sub_integral_le hF hL hFL hN (mem_Icc.mp hk).1)
    ArithmeticFunction.vonMangoldt_nonneg).trans_eq (by ring)

/-- Every fixed finite prime-power source is the limit of its terminal arithmetic sums. -/
theorem tendsto_finitePrime_riemannSum
    {F : ℝ → ℝ} {B L : ℝ} (hF : ∀ x, |F x| ≤ B) (hL : 0 ≤ L)
    (hFL : ∀ x y, |F x - F y| ≤ L * |x - y|) (K : ℕ) :
    Tendsto (fun N : ℕ =>
      ∑ k ∈ Icc 1 K, (Λ k : ℝ) * ((∑ n ∈ Icc 1 (N / k), F ((n : ℝ) / N)) / N))
      atTop (𝓝 (finitePrimeTerminalMean F K)) := by
  have hlim := (tendsto_const_div_atTop_nhds_zero_nat (L + B)).mul_const
    (∑ k ∈ Icc 1 K, (Λ k : ℝ))
  simp only [zero_mul] at hlim
  have hz : Tendsto (fun N : ℕ =>
      (∑ k ∈ Icc 1 K, (Λ k : ℝ) * ((∑ n ∈ Icc 1 (N / k), F ((n : ℝ) / N)) / N)) -
        finitePrimeTerminalMean F K) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs]
    exact abs_finitePrime_riemannSum_sub_mean_le hF hL hFL hN K
  simpa only [zero_add, sub_add_cancel] using hz.add_const (finitePrimeTerminalMean F K)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.sum_terminal_hyperbola_eq_finite
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_finitePrime_riemannSum_sub_mean_le
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_finitePrime_riemannSum
