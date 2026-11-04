import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.UpwardProfileNormalization
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.LiteralUpwardKernelBounds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.LiteralUpwardKernelSupport

/-!
# The two literal upward offset rows

Positive and negative offsets retain their original horizon cutoffs.
Their sum is exactly the reciprocal-profile coefficient. Kernel support,
uniform amplitude and variation remain available for each sign separately.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory

/-- The positive logarithmic offset with its actual horizon cutoff. -/
def positiveLiteralUpwardKernel (φ : ℝ → ℝ) (c : ℝ) (N k h n : ℕ) : ℝ :=
  if k * n + h ≤ N then logarithmicUpwardKernel φ c N (k * n) (k * n + h) else 0

/-- The negative logarithmic offset, excluding the origin and retaining its horizon cutoff. -/
def negativeLiteralUpwardKernel (φ : ℝ → ℝ) (c : ℝ) (N k h n : ℕ) : ℝ :=
  if h < k * n ∧ k * n - h ≤ N then
    logarithmicUpwardKernel φ c N (k * n) (k * n - h) else 0

def positiveLiteralUpwardRow (φ : ℝ → ℝ) (c : ℝ) (B N : ℕ) (F : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 (N + B), (ArithmeticFunction.vonMangoldt k : ℝ) / k *
    ∑ h ∈ Icc 1 B, F (k * n + h) * positiveLiteralUpwardKernel φ c N k h n

def negativeLiteralUpwardRow (φ : ℝ → ℝ) (c : ℝ) (B N : ℕ) (F : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 (N + B), (ArithmeticFunction.vonMangoldt k : ℝ) / k *
    ∑ h ∈ Icc 1 B, F (k * n - h) * negativeLiteralUpwardKernel φ c N k h n

/-- Separating the signs changes neither the source nor either finite cutoff. -/
theorem logarithmicUpwardProfileCoefficient_eq_rows (φ : ℝ → ℝ) (c : ℝ)
    (B N : ℕ) (F : ℕ → ℝ) (n : ℕ) :
    logarithmicUpwardProfileCoefficient φ c B N F n =
      (positiveLiteralUpwardRow φ c B N F n + negativeLiteralUpwardRow φ c B N F n) /
        (∫ u, φ u ^ 2) := by
  have he (k h : ℕ) : logarithmicUpwardProfileOffset φ c N F n k h =
      F (k * n + h) * positiveLiteralUpwardKernel φ c N k h n +
        F (k * n - h) * negativeLiteralUpwardKernel φ c N k h n := by
    simp only [logarithmicUpwardProfileOffset, positiveLiteralUpwardKernel,
      negativeLiteralUpwardKernel, mul_ite, mul_zero]
  simp only [logarithmicUpwardProfileCoefficient, he, sum_add_distrib, mul_add]
  rw [sum_add_distrib]
  change (1 / (∫ u, φ u ^ 2)) *
      (positiveLiteralUpwardRow φ c B N F n + negativeLiteralUpwardRow φ c B N F n) = _
  ring

/-- Both cutoff kernels remain nonnegative for a nonnegative atom. -/
theorem literalUpwardKernels_nonneg {φ : ℝ → ℝ} (hφ0 : ∀ u, 0 ≤ φ u)
    (c : ℝ) (N k h n : ℕ) :
    0 ≤ positiveLiteralUpwardKernel φ c N k h n ∧
      0 ≤ negativeLiteralUpwardKernel φ c N k h n := by
  constructor
  · dsimp only [positiveLiteralUpwardKernel]
    split_ifs
    · exact logarithmicUpwardKernel_nonneg hφ0 c N (k * n) (k * n + h)
    · exact le_rfl
  · dsimp only [negativeLiteralUpwardKernel]
    split_ifs
    · exact logarithmicUpwardKernel_nonneg hφ0 c N (k * n) (k * n - h)
    · exact le_rfl

/-- Both signed cutoff kernels have a uniform square-mass amplitude away from the offset origin. -/
theorem abs_literalUpwardKernels_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (c : ℝ) (N : ℕ)
    {k h n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (haway : 2 * h ≤ k * n) :
    |positiveLiteralUpwardKernel φ c N k h n| ≤ 2 * ∫ u, φ u ^ 2 ∧
      |negativeLiteralUpwardKernel φ c N k h n| ≤ 2 * ∫ u, φ u ^ 2 := by
  have hmass : 0 ≤ 2 * ∫ u, φ u ^ 2 := by
    exact mul_nonneg zero_le_two (integral_nonneg fun u => sq_nonneg (φ u))
  constructor
  · dsimp only [positiveLiteralUpwardKernel]
    split_ifs
    · exact abs_logarithmicUpwardKernel_positive_le hφ hsupp c N h hk hn
    · simpa only [abs_zero] using hmass
  · dsimp only [negativeLiteralUpwardKernel]
    split_ifs
    · exact abs_logarithmicUpwardKernel_negative_le hφ hsupp c N hk hn haway
    · simpa only [abs_zero] using hmass

/-- The positive finite cutoff has precisely the supported multiplier interval. -/
theorem positiveLiteralUpwardKernel_support {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    {N k h n : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) (hh : 1 ≤ h) (hn : 1 ≤ n)
    (hwidth : c / N ≤ 1) (hker : positiveLiteralUpwardKernel φ c N k h n ≠ 0) :
    k ∈ Icc ⌈(N : ℝ) / (c * Real.exp 1 * n)⌉₊
      ⌊((N : ℝ) + linearPrimeStrip c) / n⌋₊ := by
  unfold positiveLiteralUpwardKernel at hker
  split_ifs at hker with hcut
  · exact logarithmic_kernel_nat_interval hφ hsupp hc hN hk hn
      (mem_Icc.mpr ⟨by omega, hcut⟩) (by omega) hwidth hker
  · exact False.elim (hker rfl)

/-- The negative finite cutoff preserves the same exact multiplier interval. -/
theorem negativeLiteralUpwardKernel_support {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    {N k h n : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) (hh : 1 ≤ h) (hn : 1 ≤ n)
    (hwidth : c / N ≤ 1) (hker : negativeLiteralUpwardKernel φ c N k h n ≠ 0) :
    k ∈ Icc ⌈(N : ℝ) / (c * Real.exp 1 * n)⌉₊
      ⌊((N : ℝ) + linearPrimeStrip c) / n⌋₊ := by
  unfold negativeLiteralUpwardKernel at hker
  split_ifs at hker with hcut
  · exact logarithmic_kernel_nat_interval hφ hsupp hc hN hk hn
      (mem_Icc.mpr ⟨by omega, hcut.2⟩) (by omega) hwidth hker
  · exact False.elim (hker rfl)

/-- Every active literal kernel is uniformly bounded once integer separation dominates the strip. -/
theorem abs_literalUpwardKernels_le_of_separation {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    {N B k h n : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) (hh : h ∈ Icc 1 B) (hn : 1 ≤ n)
    (hwidth : c / N ≤ 1) (hsep : 2 * c * Real.exp 1 * B ≤ N) :
    |positiveLiteralUpwardKernel φ c N k h n| ≤ 2 * ∫ u, φ u ^ 2 ∧
      |negativeLiteralUpwardKernel φ c N k h n| ≤ 2 * ∫ u, φ u ^ 2 := by
  have hmass : 0 ≤ 2 * ∫ u, φ u ^ 2 :=
    mul_nonneg zero_le_two (integral_nonneg fun u => sq_nonneg (φ u))
  constructor
  · dsimp only [positiveLiteralUpwardKernel]
    split_ifs
    · exact abs_logarithmicUpwardKernel_positive_le hφ hsupp c N h hk hn
    · simpa only [abs_zero] using hmass
  · dsimp only [negativeLiteralUpwardKernel]
    split_ifs with hcut
    · by_cases hker : logarithmicUpwardKernel φ c N (k * n) (k * n - h) = 0
      · simpa only [hker, abs_zero] using hmass
      · have haway := logarithmic_kernel_twice_offset_le hφ hsupp hc hN hk hn
          (mem_Icc.mpr ⟨by omega, hcut.2⟩) (by have := (mem_Icc.mp hh).1; omega)
          hwidth (mem_Icc.mp hh).2 hsep hker
        exact abs_logarithmicUpwardKernel_negative_le hφ hsupp c N hk hn haway
    · simpa only [abs_zero] using hmass

/-- One atom-dependent constant controls variation of both literal cutoff kernels. -/
theorem exists_literalUpwardKernels_variation {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c : ℝ}, 0 < c → ∀ {A Z N k h : ℕ},
      1 ≤ A → A ≤ Z → 1 ≤ k → 2 * h ≤ A →
      discreteVariation (positiveLiteralUpwardKernel φ c N k h) A Z ≤ C ∧
      discreteVariation (negativeLiteralUpwardKernel φ c N k h) A Z ≤ C := by
  simpa only [positiveLiteralUpwardKernel, negativeLiteralUpwardKernel] using
    exists_literal_upward_kernel_variation hφ hsupp

#print axioms abs_literalUpwardKernels_le_of_separation
#print axioms exists_literalUpwardKernels_variation

#print axioms logarithmicUpwardProfileCoefficient_eq_rows
#print axioms abs_literalUpwardKernels_le
#print axioms positiveLiteralUpwardKernel_support
#print axioms negativeLiteralUpwardKernel_support

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
