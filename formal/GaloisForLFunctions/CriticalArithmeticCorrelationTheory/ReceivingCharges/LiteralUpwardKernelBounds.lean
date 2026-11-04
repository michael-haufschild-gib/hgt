import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.LiteralUpwardKernelVariation
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheUpwardPrimeWindowsCarryTheShellCorrection

/-!
# Uniform bounds for the actual upward kernels

The autocorrelation mass bounds both shifted kernels away from the excluded
origin. Smooth compact support supplies the Lipschitz constant needed for
their uniform variation; no extra analytic premise remains.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell

/-- A nonnegative atom gives a nonnegative literal logarithmic kernel. -/
theorem logarithmicUpwardKernel_nonneg {φ : ℝ → ℝ} (hφ0 : ∀ u, 0 ≤ φ u)
    (c : ℝ) (N T j : ℕ) : 0 ≤ logarithmicUpwardKernel φ c N T j := by
  apply mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  exact integral_nonneg fun u => mul_nonneg (hφ0 u) (hφ0 _)

/-- The positive shifted kernel is bounded by twice the atom's square mass. -/
theorem abs_logarithmicUpwardKernel_positive_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (c : ℝ) (N h : ℕ)
    {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    |logarithmicUpwardKernel φ c N (k * n) (k * n + h)| ≤ 2 * ∫ u, φ u ^ 2 := by
  rw [actual_positive_kernel_formula φ c N h hk hn, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul
    (positive_root_ratio_le (by positivity : 0 ≤ (h : ℝ) / k) (by exact_mod_cast hn))
    (abs_shellAutocorr_le hφ hsupp _) (abs_nonneg _) zero_le_two

/-- The negative shifted kernel has the same bound when its product index exceeds twice the offset. -/
theorem abs_logarithmicUpwardKernel_negative_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (c : ℝ) (N : ℕ)
    {k n h : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (haway : 2 * h ≤ k * n) :
    |logarithmicUpwardKernel φ c N (k * n) (k * n - h)| ≤ 2 * ∫ u, φ u ^ 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hT : 0 < k * n := Nat.mul_pos hk hn
  have hh : h < k * n := by omega
  have ha : 2 * ((h : ℝ) / k) ≤ (n : ℝ) := by
    rw [← mul_div_assoc, div_le_iff₀ hk0]
    have h : 2 * (h : ℝ) ≤ (k : ℝ) * n := by exact_mod_cast haway
    simpa only [mul_comm] using h
  rw [actual_negative_kernel_formula φ c N hk hn hh, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul (negative_root_ratio_le hn0 ha)
    (abs_shellAutocorr_le hφ hsupp _) (abs_nonneg _) zero_le_two

/-- Smooth compact support supplies a single variation constant for both literal cutoff kernels. -/
theorem exists_literal_upward_kernel_variation {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c : ℝ}, 0 < c → ∀ {A Z N k h : ℕ},
      1 ≤ A → A ≤ Z → 1 ≤ k → 2 * h ≤ A →
      discreteVariation (fun n => if k * n + h ≤ N then
        logarithmicUpwardKernel φ c N (k * n) (k * n + h) else 0) A Z ≤ C ∧
      discreteVariation (fun n => if h < k * n ∧ k * n - h ≤ N then
        logarithmicUpwardKernel φ c N (k * n) (k * n - h) else 0) A Z ≤ C := by
  obtain ⟨K, hK, hLip⟩ := exists_shellAutocorr_lipschitz hφ hsupp
  have hmass : 0 ≤ ∫ u, φ u ^ 2 := integral_nonneg fun u => sq_nonneg (φ u)
  refine ⟨2 * K + 4 * (∫ u, φ u ^ 2), by positivity, ?_⟩
  intro c hc A Z N k h hA hAZ hk haway
  have hzero : ∀ x, 1 ≤ x → shellAutocorr φ x = 0 :=
    fun x hx => shellAutocorr_eq_zero_of_one_le hφ hsupp hx
  exact ⟨actual_positive_kernel_variation hmass hK hLip hzero
      (abs_shellAutocorr_le hφ hsupp) hc hA hAZ hk,
    actual_negative_kernel_variation hmass hK hLip hzero
      (abs_shellAutocorr_le hφ hsupp) hc hA hAZ hk haway⟩

#print axioms logarithmicUpwardKernel_nonneg
#print axioms abs_logarithmicUpwardKernel_negative_le
#print axioms exists_literal_upward_kernel_variation

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
