import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureUniformGridAliasNoGo
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Finite.Comparison

/-!+# Entropy cost of a critical-feature phase alias

Apply the paper's proven finite-law Pinsker estimate to the actual HCF boundary
reporter. Its native 37/200 envelope makes any departure from the equal-weight
grid alias cost at least the square of that departure in relative entropy.
The reference grid alias is exactly the corpus's existing physical alias.
-/

open GaloisForLFunctions.HTGeometry FourierLLogL
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Expected physical boundary alias of a finite phase law. -/
def paperCriticalFeatureLawAlias {α : Type*} [Fintype α]
    (P : Law α) (phase : α → ℝ) : ℝ :=
  P.Ex fun a => criticalFeatureRealBoundaryPeriodization (phase a) - 2 * Real.pi

/-- The actual reporter's sharp envelope converts phase-law distance to alias error. -/
theorem paperCriticalFeatureLawAlias_tv {α : Type*} [Fintype α]
    (P Q : Law α) (phase : α → ℝ) :
    |paperCriticalFeatureLawAlias P phase - paperCriticalFeatureLawAlias Q phase| ≤
      (37 : ℝ) / 100 * P.tv Q := by
  classical
  unfold paperCriticalFeatureLawAlias Law.Ex
  rw [← Finset.sum_sub_distrib]
  simp only [← sub_mul]
  calc
    |∑ a, (P a - Q a) *
        (criticalFeatureRealBoundaryPeriodization (phase a) - 2 * Real.pi)| ≤
      ∑ a, |(P a - Q a) *
        (criticalFeatureRealBoundaryPeriodization (phase a) - 2 * Real.pi)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |P a - Q a| * ((37 : ℝ) / 200) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_criticalFeatureRealBoundaryPeriodization_sub_two_pi_le (phase a)) (abs_nonneg _)
    _ = (37 : ℝ) / 100 * P.tv Q := by rw [← Finset.sum_mul, Law.tv]; ring

/-- Relative entropy to the uniform law is exactly the Shannon entropy deficit. -/
theorem paperCriticalFeatureLaw_uniform_kl {α : Type*} [Fintype α] [Nonempty α]
    (P : Law α) : P.kl (Law.uniform α) = Real.log (Fintype.card α : ℝ) - P.entropy := by
  unfold Law.kl Law.crossE
  simp_rw [Law.uniform_apply, Real.log_inv, neg_neg, Law.Ex_const]

/-- No domination assumption is needed: the reference law is strictly positive. -/
theorem paperCriticalFeatureLawAlias_uniform_entropy {α : Type*} [Fintype α] [Nonempty α]
    (P : Law α) (phase : α → ℝ) :
    |paperCriticalFeatureLawAlias P phase -
        paperCriticalFeatureLawAlias (Law.uniform α) phase| ≤
      (37 : ℝ) / 100 * Real.sqrt (Real.log (Fintype.card α : ℝ) - P.entropy) := by
  have hdom : P.dominated (Law.uniform α) := by
    intro a _
    rw [Law.uniform_apply]
    positivity
  have hp := Law.tv_le_sqrt_kl hdom
  rw [paperCriticalFeatureLaw_uniform_kl] at hp
  exact (paperCriticalFeatureLawAlias_tv P (Law.uniform α) phase).trans
    (mul_le_mul_of_nonneg_left hp (by positivity))

/-- The finite uniform reference is exactly the native equal-weight grid alias. -/
theorem paperCriticalFeatureLawAlias_uniform_grid (N : ℕ) :
    paperCriticalFeatureLawAlias (Law.uniform (Fin (N + 1)))
        (fun i => uniformNode 0 1 (N + 1) i) =
      (criticalFeatureUniformGridAlias (N + 1)).re := by
  simp only [paperCriticalFeatureLawAlias, Law.Ex, Law.uniform_apply, Fintype.card_fin,
    criticalFeatureUniformGridAlias, Complex.re_sum, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  simpa only [one_div] using Fin.sum_univ_eq_sum_range
    (fun i : ℕ => (((N + 1 : ℕ) : ℝ))⁻¹ *
      (criticalFeatureRealBoundaryPeriodization (uniformNode 0 1 (N + 1) i) - 2 * Real.pi))
    (N + 1)

/-- Entropy deficit pays for every weighted-grid improvement over the native uniform alias. -/
theorem paperCriticalFeatureGridAlias_entropy (N : ℕ) (P : Law (Fin (N + 1))) :
    |paperCriticalFeatureLawAlias P (fun i => uniformNode 0 1 (N + 1) i) -
        (criticalFeatureUniformGridAlias (N + 1)).re| ≤
      (37 : ℝ) / 100 * Real.sqrt (Real.log ((N + 1 : ℕ) : ℝ) - P.entropy) := by
  simpa only [Fintype.card_fin, paperCriticalFeatureLawAlias_uniform_grid] using
    paperCriticalFeatureLawAlias_uniform_entropy P (fun i => uniformNode 0 1 (N + 1) i)

end

end RHTower
