import GaloisForLFunctions.BezoutValuationIncidence.Sieve.LogarithmicKernelVariation
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheUpwardPrimeRowsRealizeTheCompletedShellCorrection

/-!
# Variation of the literal upward logarithmic kernels

The exact square-root Jacobian and logarithmic argument match monotone
kernels with offset `h/k`. Both signs retain their original horizon
cutoffs, with variation bounded independently of all horizon scales.
-/

noncomputable section
set_option autoImplicit false
open Finset
open GaloisForLFunctions
open BezoutValuationIncidence CriticalArithmeticCorrelationTheory
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

/-- The literal positive kernel is the monotone logarithmic kernel with offset `h/k`. -/
theorem actual_positive_kernel_formula (φ : ℝ → ℝ) (c : ℝ) (N h : ℕ)
    {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    logarithmicUpwardKernel φ c N (k * n) (k * n + h) =
      Real.sqrt ((n : ℝ) / ((n : ℝ) + (h : ℝ) / k)) *
        shellAutocorr φ ((N : ℝ) / c * Real.log (1 + ((h : ℝ) / k) / n)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hT0 : (0 : ℝ) < (k : ℝ) * n := mul_pos hk0 hn0
  have hj0 : (0 : ℝ) < (k : ℝ) * n + h := add_pos_of_pos_of_nonneg hT0 (Nat.cast_nonneg h)
  have hden : (0 : ℝ) < (n : ℝ) + (h : ℝ) / k :=
    add_pos_of_pos_of_nonneg hn0 (div_nonneg (Nat.cast_nonneg h) hk0.le)
  have hfrac : ((k : ℝ) * n) / ((k : ℝ) * n + h) =
      (n : ℝ) / ((n : ℝ) + (h : ℝ) / k) := by
    field_simp [hk0.ne', hj0.ne', hden.ne']
  have hratio : ((k : ℝ) * n + h) / ((k : ℝ) * n) = 1 + ((h : ℝ) / k) / n := by
    field_simp [hk0.ne', hn0.ne']
  rw [logarithmicUpwardKernel, Nat.cast_mul, Nat.cast_add, Nat.cast_mul,
    ← Real.sqrt_div hT0.le, hfrac, ← Real.log_div hj0.ne' hT0.ne', hratio]

/-- Evenness of autocorrelation turns the negative logarithmic offset into a nonnegative argument. -/
theorem actual_negative_kernel_formula (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    {k n h : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hh : h < k * n) :
    logarithmicUpwardKernel φ c N (k * n) (k * n - h) =
      Real.sqrt ((n : ℝ) / ((n : ℝ) - (h : ℝ) / k)) *
        shellAutocorr φ ((N : ℝ) / c * (-Real.log (1 - ((h : ℝ) / k) / n))) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hT0 : (0 : ℝ) < (k : ℝ) * n := mul_pos hk0 hn0
  have hhR : (h : ℝ) < (k : ℝ) * n := by exact_mod_cast hh
  have hj0 : (0 : ℝ) < (k : ℝ) * n - h := sub_pos.mpr hhR
  have hden : (0 : ℝ) < (n : ℝ) - (h : ℝ) / k := by
    apply sub_pos.mpr
    apply (div_lt_iff₀ hk0).mpr
    simpa only [mul_comm] using hhR
  have hfrac : ((k : ℝ) * n) / ((k : ℝ) * n - h) =
      (n : ℝ) / ((n : ℝ) - (h : ℝ) / k) := by
    field_simp [hk0.ne', hj0.ne', hden.ne']
  have hratio : ((k : ℝ) * n - h) / ((k : ℝ) * n) = 1 - ((h : ℝ) / k) / n := by
    field_simp [hk0.ne', hn0.ne']
  rw [logarithmicUpwardKernel, Nat.cast_sub hh.le, Nat.cast_mul,
    ← Real.sqrt_div hT0.le, hfrac, ← Real.log_div hj0.ne' hT0.ne', hratio]
  rw [show (N : ℝ) / c * Real.log (1 - ((h : ℝ) / k) / n) =
    -((N : ℝ) / c * (-Real.log (1 - ((h : ℝ) / k) / n))) by ring, shellAutocorr_neg]

#print axioms actual_positive_kernel_formula
#print axioms actual_negative_kernel_formula

/-- The positive literal horizon cutoff preserves a scale-independent kernel variation bound. -/
theorem actual_positive_kernel_variation {φ : ℝ → ℝ} {M K : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hf : ∀ x y, |shellAutocorr φ x - shellAutocorr φ y| ≤ K * |x - y|)
    (hf1 : ∀ x, 1 ≤ x → shellAutocorr φ x = 0) (hfM : ∀ x, |shellAutocorr φ x| ≤ M)
    {c : ℝ} (hc : 0 < c) {A Z N k h : ℕ} (hA : 1 ≤ A) (hAZ : A ≤ Z) (hk : 1 ≤ k) :
    discreteVariation (fun n => if k * n + h ≤ N then
      logarithmicUpwardKernel φ c N (k * n) (k * n + h) else 0) A Z ≤ 2 * K + 4 * M := by
  let f : ℕ → ℝ := fun n => Real.sqrt ((n : ℝ) / ((n : ℝ) + (h : ℝ) / k)) *
    shellAutocorr φ ((N : ℝ) / c * Real.log (1 + ((h : ℝ) / k) / n))
  have ha : 0 ≤ (h : ℝ) / k := by positivity
  have hfbound : ∀ n ∈ Icc A Z, |f n| ≤ 2 * M := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hA.trans (mem_Icc.mp hn).1
    dsimp only [f]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul (positive_root_ratio_le ha hn0) (hfM _) (abs_nonneg _) zero_le_two
  have hfvar : discreteVariation f A Z ≤ 2 * K + 2 * M :=
    positive_log_kernel_variation hM hK ha (div_nonneg (Nat.cast_nonneg N) hc.le)
      hf hf1 hfM hA hAZ
  have hcut := cutoff_variation (mul_nonneg zero_le_two hM) hAZ hfbound hfvar
    (fun n => k * n + h ≤ N) (by
      intro n m _ hnm _ hm
      have hmul := Nat.mul_le_mul_left k hnm
      omega)
  have he : discreteVariation (fun n => if k * n + h ≤ N then
      logarithmicUpwardKernel φ c N (k * n) (k * n + h) else 0) A Z =
      discreteVariation (fun n => if k * n + h ≤ N then f n else 0) A Z := by
    apply discreteVariation_congr
    intro n hn
    by_cases hcut : k * n + h ≤ N
    · rw [if_pos hcut, if_pos hcut, actual_positive_kernel_formula φ c N h hk
        (hA.trans (mem_Icc.mp hn).1)]
    · rw [if_neg hcut, if_neg hcut]
  rw [he]
  exact hcut.trans_eq (by ring)

/-- Both positivity and horizon conditions remain in the negative literal kernel bound. -/
theorem actual_negative_kernel_variation {φ : ℝ → ℝ} {M K : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hf : ∀ x y, |shellAutocorr φ x - shellAutocorr φ y| ≤ K * |x - y|)
    (hf1 : ∀ x, 1 ≤ x → shellAutocorr φ x = 0) (hfM : ∀ x, |shellAutocorr φ x| ≤ M)
    {c : ℝ} (hc : 0 < c) {A Z N k h : ℕ} (hA : 1 ≤ A) (hAZ : A ≤ Z)
    (hk : 1 ≤ k) (haway : 2 * h ≤ A) :
    discreteVariation (fun n => if h < k * n ∧ k * n - h ≤ N then
      logarithmicUpwardKernel φ c N (k * n) (k * n - h) else 0) A Z ≤ 2 * K + 4 * M := by
  let f : ℕ → ℝ := fun n => Real.sqrt ((n : ℝ) / ((n : ℝ) - (h : ℝ) / k)) *
    shellAutocorr φ ((N : ℝ) / c * (-Real.log (1 - ((h : ℝ) / k) / n)))
  have ha : 0 ≤ (h : ℝ) / k := by positivity
  have hak : (h : ℝ) / k ≤ h := div_le_self (Nat.cast_nonneg h) (by exact_mod_cast hk)
  have hawayR : 2 * ((h : ℝ) / k) ≤ (A : ℝ) :=
    (mul_le_mul_of_nonneg_left hak zero_le_two).trans (by exact_mod_cast haway)
  have hpositive (n : ℕ) (hn : A ≤ n) : h < k * n := by
    have hmul : n ≤ k * n := by simpa only [one_mul] using Nat.mul_le_mul_right n hk
    omega
  have hfbound : ∀ n ∈ Icc A Z, |f n| ≤ 2 * M := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hA.trans (mem_Icc.mp hn).1
    have hnaway : 2 * ((h : ℝ) / k) ≤ (n : ℝ) :=
      hawayR.trans (by exact_mod_cast (mem_Icc.mp hn).1)
    dsimp only [f]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul (negative_root_ratio_le hn0 hnaway) (hfM _) (abs_nonneg _) zero_le_two
  have hfvar : discreteVariation f A Z ≤ 2 * K + 2 * M :=
    negative_log_kernel_variation hM hK ha (div_nonneg (Nat.cast_nonneg N) hc.le)
      hf hf1 hfM hA hAZ hawayR
  have hcut := cutoff_variation (mul_nonneg zero_le_two hM) hAZ hfbound hfvar
    (fun n => h < k * n ∧ k * n - h ≤ N) (by
      intro n m hn hnm _ hm
      refine ⟨hpositive n hn, ?_⟩
      have hmul := Nat.mul_le_mul_left k hnm
      omega)
  have he : discreteVariation (fun n => if h < k * n ∧ k * n - h ≤ N then
      logarithmicUpwardKernel φ c N (k * n) (k * n - h) else 0) A Z =
      discreteVariation (fun n => if h < k * n ∧ k * n - h ≤ N then f n else 0) A Z := by
    apply discreteVariation_congr
    intro n hn
    by_cases hcut : h < k * n ∧ k * n - h ≤ N
    · rw [if_pos hcut, if_pos hcut, actual_negative_kernel_formula φ c N hk
        (hA.trans (mem_Icc.mp hn).1) hcut.1]
    · rw [if_neg hcut, if_neg hcut]
  rw [he]
  exact hcut.trans_eq (by ring)

#print axioms actual_positive_kernel_variation
#print axioms actual_negative_kernel_variation

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
