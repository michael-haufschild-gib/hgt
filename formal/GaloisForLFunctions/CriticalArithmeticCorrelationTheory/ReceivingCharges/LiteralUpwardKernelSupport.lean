import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.UpwardProfileOffsets
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheUpwardPrimeRowsRealizeTheCompletedShellCorrection

/-!
# Exact multiplier support of literal upward kernels

Integer separation confines every nonzero offset to a multiplier interval
of logarithmic width at most `log(2e*c)`. Natural endpoints preserve both
finite horizon cutoffs.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell

/-- A nonzero literal kernel forces the exact logarithmic support inequality. -/
theorem logarithmic_kernel_support {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    {N T j : ℕ} (hN : 1 ≤ N) (hkernel : logarithmicUpwardKernel φ c N T j ≠ 0) :
    |Real.log j - Real.log T| < c / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hscale : 0 < (N : ℝ) / c := div_pos hN0 hc
  have hcorr : shellAutocorr φ ((N : ℝ) / c * (Real.log j - Real.log T)) ≠ 0 := by
    intro h
    apply hkernel
    rw [logarithmicUpwardKernel, h, mul_zero]
  have harg : |(N : ℝ) / c * (Real.log j - Real.log T)| < 1 := by
    by_contra h
    exact hcorr (shellAutocorr_eq_zero_of_one_le_abs hφ hsupp (le_of_not_gt h))
  rw [abs_mul, abs_of_pos hscale] at harg
  have h : |Real.log j - Real.log T| < 1 / ((N : ℝ) / c) :=
    (lt_div_iff₀ hscale).mpr (by simpa only [mul_comm] using harg)
  simpa only [one_div_div, one_mul] using h

/-- Literal support confines each multiplier to an interval of ratio proportional to overlap. -/
theorem logarithmic_kernel_multiplier_interval {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    {N k n j : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hj : j ∈ Icc 1 N) (hne : k * n ≠ j) (hwidth : c / N ≤ 1)
    (hkernel : logarithmicUpwardKernel φ c N (k * n) j ≠ 0) :
    (N : ℝ) / (c * Real.exp 1 * n) ≤ k ∧
      (k : ℝ) ≤ ((N : ℝ) + linearPrimeStrip c) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hT : 1 ≤ k * n := Nat.mul_pos hk hn
  have hlog := (logarithmic_kernel_support hφ hsupp hc hN hkernel).le
  have hsep := (logWindow_integer_separation_small_width hc hN hT (mem_Icc.mp hj).1 hne hlog hwidth).1
  have hdist := upward_product_distance_le_small_width hc hT hj
    (by simpa only [abs_sub_comm] using hlog) hwidth
  constructor
  · apply (div_le_iff₀ (mul_pos (mul_pos hc (Real.exp_pos 1)) hn0)).mpr
    simpa only [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hsep
  · apply (le_div_iff₀ hn0).mpr
    have hupper := (abs_le.mp hdist).2
    have hjN : (j : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hj).2
    push_cast at hupper
    linarith only [hupper, hjN]

/-- The natural multiplier endpoints preserve the complete finite support. -/
theorem logarithmic_kernel_nat_interval {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    {N k n j : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hj : j ∈ Icc 1 N) (hne : k * n ≠ j) (hwidth : c / N ≤ 1)
    (hkernel : logarithmicUpwardKernel φ c N (k * n) j ≠ 0) :
    k ∈ Icc ⌈(N : ℝ) / (c * Real.exp 1 * n)⌉₊
      ⌊((N : ℝ) + linearPrimeStrip c) / n⌋₊ := by
  obtain ⟨hlo, hhi⟩ := logarithmic_kernel_multiplier_interval hφ hsupp hc hN hk hn hj hne hwidth hkernel
  exact mem_Icc.mpr ⟨Nat.ceil_le.mpr hlo, (Nat.le_floor_iff (by positivity)).mpr hhi⟩

/-- The supported multiplier interval has a uniform logarithmic width. -/
theorem multiplier_interval_log_width {c : ℝ} (hc : 0 < c)
    {N n B H X : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n) (hB : B ≤ N) (hHX : H ≤ X)
    (hH : H = ⌈(N : ℝ) / (c * Real.exp 1 * n)⌉₊)
    (hX : X = ⌊((N : ℝ) + B) / n⌋₊) :
    1 ≤ H ∧ Real.log X - Real.log H ≤ Real.log (2 * c * Real.exp 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < c * Real.exp 1 * n := by positivity
  have hlo : (N : ℝ) / (c * Real.exp 1 * n) ≤ H := by rw [hH]; exact Nat.le_ceil _
  have hH0 : (0 : ℝ) < H := (div_pos hN0 hden).trans_le hlo
  have hX0 : (0 : ℝ) < X := hH0.trans_le (by exact_mod_cast hHX)
  have hhi : (X : ℝ) ≤ ((N : ℝ) + B) / n := by
    rw [hX]
    exact Nat.floor_le (by positivity)
  have hBr : (B : ℝ) ≤ N := by exact_mod_cast hB
  have hratio : (X : ℝ) / H ≤ 2 * c * Real.exp 1 := by
    apply (div_le_iff₀ hH0).mpr
    have hlo' := (div_le_iff₀ hden).mp hlo
    have hhi' := (le_div_iff₀ hn0).mp hhi
    apply (mul_le_mul_iff_right₀ hn0).mp
    nlinarith only [hBr, hlo', hhi']
  refine ⟨by exact_mod_cast hH0, ?_⟩
  rw [← Real.log_div hX0.ne' hH0.ne']
  exact Real.log_le_log (div_pos hX0 hH0) hratio

/-- Macroscopic integer separation keeps every nonzero offset at most half its product index. -/
theorem logarithmic_kernel_twice_offset_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    {N k n j B h : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hj : j ∈ Icc 1 N) (hne : k * n ≠ j) (hwidth : c / N ≤ 1)
    (hhB : h ≤ B) (hsep : 2 * c * Real.exp 1 * B ≤ N)
    (hkernel : logarithmicUpwardKernel φ c N (k * n) j ≠ 0) :
    2 * h ≤ k * n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hce : 0 < c * Real.exp 1 := mul_pos hc (Real.exp_pos 1)
  have hlo := (logarithmic_kernel_multiplier_interval hφ hsupp hc hN hk hn hj hne hwidth hkernel).1
  have hprod := (div_le_iff₀ (mul_pos hce hn0)).mp hlo
  have hhBr : (h : ℝ) ≤ B := by exact_mod_cast hhB
  have hhce := mul_le_mul_of_nonneg_right hhBr hce.le
  have haway : 2 * (h : ℝ) ≤ (k : ℝ) * n := by
    apply (mul_le_mul_iff_right₀ hce).mp
    nlinarith only [hhce, hsep, hprod]
  exact_mod_cast haway

#print axioms logarithmic_kernel_twice_offset_le

#print axioms logarithmic_kernel_nat_interval
#print axioms multiplier_interval_log_width

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
