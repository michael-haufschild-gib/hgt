import GaloisForLFunctions.RHTower.Sieve.VonMangoldtBlockEstimate

/-!
# The type-I pieces summed only over the support of their coefficients

Both type-I coefficients are supported on an initial segment: `Λ_U ∗ μ_V` below `UV` and `μ_V`
below `V`.  Restricting the divisor sum to that segment is what makes the type-I total small, and
it also confines the curvature hypothesis to the same range — beyond it the hypothesis is false,
but the coefficient vanishes.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction RHTower

noncomputable section

/-- The truncated convolution is supported below the product of the truncations. -/
theorem truncAF_conv_apply_of_gt {f g : ArithmeticFunction ℝ} {U V n : ℕ} (h : U * V < n) :
    (truncAF f U * truncAF g V) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hp
  by_cases h1 : p.1 ≤ U
  · have h2 : ¬ (p.2 ≤ V) := by
      intro h2
      have : p.1 * p.2 ≤ U * V := Nat.mul_le_mul h1 h2
      omega
    rw [truncAF_apply_of_gt (by omega : V < p.2), mul_zero]
  · rw [truncAF_apply_of_gt (by omega : U < p.1), zero_mul]

/-- A sum against a coefficient supported on an initial segment restricts to that segment. -/
theorem sum_Icc_restrict_of_support {K L : ℕ} (hKL : K ≤ L) (g : ℕ → ℂ) (F : ℕ → ℂ)
    (hsupp : ∀ b, K < b → g b = 0) :
    (∑ b ∈ Finset.Icc 1 L, g b * F b) = ∑ b ∈ Finset.Icc 1 K, g b * F b := by
  refine (Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hKL) fun b hb hnot => ?_).symm
  rw [Finset.mem_Icc] at hb
  have : K < b := by
    by_contra hcon
    exact hnot (Finset.mem_Icc.2 ⟨hb.1, by omega⟩)
  rw [hsupp b this, zero_mul]

/-- **The `ζ`-convolution type-I estimate, over the support only.** -/
theorem norm_sum_zeta_conv_ndPhaseExp_le' {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {A B L K : ℕ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L) (hKL : K ≤ L) (g : ℕ → ℂ)
    (hsupp : ∀ b, K < b → g b = 0)
    (hcond : ∀ b ∈ Finset.Icc 1 K,
      r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ)
        ∧ nearDiagonalLambda T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) :
    ‖∑ n ∈ Finset.Ico A B,
        (∑ p ∈ n.divisorsAntidiagonal, (1 : ℂ) * g p.2) * ndPhaseExp T r n‖
      ≤ ∑ b ∈ Finset.Icc 1 K, ‖g b‖ * fibreBound T r A B b := by
  rw [sum_conv_mul_Ico_eq hA hB hBL (fun _ => (1 : ℂ)) g (ndPhaseExp T r),
    sum_Icc_restrict_of_support hKL g _ hsupp]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun b hb => ?_
  rw [Finset.mem_Icc] at hb
  obtain ⟨hrA, hlam⟩ := hcond b (Finset.mem_Icc.2 hb)
  have hb1 : 1 ≤ b := hb.1
  have hinner : (∑ a ∈ Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1),
      (1 : ℂ) * ndPhaseExp T r (a * b))
      = ∑ a ∈ Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1), ndExp T r a b := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [one_mul, ndPhaseExp_mul]
  rw [norm_mul, hinner]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact norm_sum_ndExp_le hT hr hb1 _ _ (Nat.le_add_left 1 _) hrA hlam

/-- **The `log`-convolution type-I estimate, over the support only.** -/
theorem norm_sum_log_conv_ndPhaseExp_le' {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {A B L K : ℕ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L) (hKL : K ≤ L) (g : ℕ → ℂ)
    (hsupp : ∀ b, K < b → g b = 0)
    (hcond : ∀ b ∈ Finset.Icc 1 K,
      r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ)
        ∧ nearDiagonalLambda T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) :
    ‖∑ n ∈ Finset.Ico A B,
        (∑ p ∈ n.divisorsAntidiagonal, ((Real.log (p.1 : ℝ) : ℝ) : ℂ) * g p.2)
          * ndPhaseExp T r n‖
      ≤ ∑ b ∈ Finset.Icc 1 K,
          ‖g b‖ * (2 * fibreBound T r A B b
            * Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ)) := by
  rw [sum_conv_mul_Ico_eq hA hB hBL (fun a => ((Real.log (a : ℝ) : ℝ) : ℂ)) g (ndPhaseExp T r),
    sum_Icc_restrict_of_support hKL g _ hsupp]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun b hb => ?_
  rw [Finset.mem_Icc] at hb
  obtain ⟨hrA, hlam⟩ := hcond b (Finset.mem_Icc.2 hb)
  have hb1 : 1 ≤ b := hb.1
  have hinner : (∑ a ∈ Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1),
      ((Real.log (a : ℝ) : ℝ) : ℂ) * ndPhaseExp T r (a * b))
      = ∑ a ∈ Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1),
          ((Real.log (a : ℝ) : ℝ) : ℂ) * ndExp T r a b := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ndPhaseExp_mul]
  rw [norm_mul, hinner]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  by_cases hlt : (A - 1) / b + 1 < (B - 1) / b + 1
  · exact norm_sum_log_ndExp_le hT hr hb1 hlt (Nat.le_add_left 1 _) hrA hlam
  · have hempty : Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1) = ∅ :=
      Finset.Ico_eq_empty (by omega)
    rw [hempty, Finset.sum_empty, norm_zero]
    have hlog : (0 : ℝ) ≤ Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ) := by
      rcases Nat.eq_zero_or_pos ((B - 1) / b + 1 - 1) with h | h
      · rw [h]
        simp
      · exact Real.log_nonneg (by exact_mod_cast h)
    have hfb : (0 : ℝ) ≤ fibreBound T r A B b := by
      rw [fibreBound]
      positivity
    positivity

end

end RHTower.Sieve
