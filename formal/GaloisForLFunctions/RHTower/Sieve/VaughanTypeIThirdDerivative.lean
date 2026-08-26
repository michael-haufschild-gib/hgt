import GaloisForLFunctions.RHTower.Sieve.VaughanTypeIRestricted
import GaloisForLFunctions.RHTower.Sieve.TypeIThirdDerivative

/-!
# Vaughan type-I pieces with the third-derivative envelope

This is the third-derivative analogue of the existing second-derivative fibre estimates.  It keeps
the coefficient support restriction, so every analytic hypothesis is required only where the
Vaughan coefficient can be nonzero.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

/-- Third-derivative envelope for the fibre at divisor `b`. -/
def thirdDerivativeFibreBound (T r : ℝ) (A B b : ℕ) : ℝ :=
  thirdDerivativeTypeIBound T r b ((A - 1) / b + 1) ((B - 1) / b + 1)

theorem thirdDerivativeFibreBound_nonneg {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B b : ℕ} (hb : 1 ≤ b) : 0 ≤ thirdDerivativeFibreBound T r A B b := by
  rw [thirdDerivativeFibreBound]
  exact thirdDerivativeTypeIBound_nonneg hT hr hb (Nat.le_add_left 1 _)

/-- A coefficient-supported `ζ`-convolution controlled by third derivatives on every fibre. -/
theorem norm_sum_zeta_conv_ndPhaseExp_third_le' {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B L K : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L) (hKL : K ≤ L)
    (g : ℕ → ℂ) (hsupp : ∀ b, K < b → g b = 0)
    (hcond : ∀ b ∈ Finset.Icc 1 K,
      ((B - 1) / b + 1) - ((A - 1) / b + 1) - 1 ≤ ((A - 1) / b + 1)
        ∧ r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ)
        ∧ nearDiagonalLambda3 T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) :
    ‖∑ n ∈ Finset.Ico A B,
        (∑ p ∈ n.divisorsAntidiagonal, (1 : ℂ) * g p.2) * ndPhaseExp T r n‖
      ≤ ∑ b ∈ Finset.Icc 1 K, ‖g b‖ * thirdDerivativeFibreBound T r A B b := by
  rw [sum_conv_mul_Ico_eq hA hB hBL (fun _ => (1 : ℂ)) g (ndPhaseExp T r),
    sum_Icc_restrict_of_support hKL g _ hsupp]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun b hb => ?_
  rw [Finset.mem_Icc] at hb
  obtain ⟨hspan, hrA, hlam⟩ := hcond b (Finset.mem_Icc.2 hb)
  have hb1 : 1 ≤ b := hb.1
  have hinner : (∑ a ∈ Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1),
      (1 : ℂ) * ndPhaseExp T r (a * b))
      = ∑ a ∈ Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1), ndExp T r a b := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [one_mul, ndPhaseExp_mul]
  rw [norm_mul, hinner, thirdDerivativeFibreBound]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact norm_sum_ndExp_third_le hT hr hb1 _ _ (Nat.le_add_left 1 _) hspan hrA hlam

/-- A coefficient-supported logarithmic convolution controlled by third derivatives. -/
theorem norm_sum_log_conv_ndPhaseExp_third_le' {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B L K : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L) (hKL : K ≤ L)
    (g : ℕ → ℂ) (hsupp : ∀ b, K < b → g b = 0)
    (hcond : ∀ b ∈ Finset.Icc 1 K,
      ((B - 1) / b + 1) - ((A - 1) / b + 1) - 1 ≤ ((A - 1) / b + 1)
        ∧ r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ)
        ∧ nearDiagonalLambda3 T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) :
    ‖∑ n ∈ Finset.Ico A B,
        (∑ p ∈ n.divisorsAntidiagonal, ((Real.log (p.1 : ℝ) : ℝ) : ℂ) * g p.2)
          * ndPhaseExp T r n‖
      ≤ ∑ b ∈ Finset.Icc 1 K, ‖g b‖ *
          (2 * thirdDerivativeFibreBound T r A B b *
            Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ)) := by
  rw [sum_conv_mul_Ico_eq hA hB hBL (fun a => ((Real.log (a : ℝ) : ℝ) : ℂ)) g
      (ndPhaseExp T r), sum_Icc_restrict_of_support hKL g _ hsupp]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun b hb => ?_
  rw [Finset.mem_Icc] at hb
  obtain ⟨hspan, hrA, hlam⟩ := hcond b (Finset.mem_Icc.2 hb)
  have hb1 : 1 ≤ b := hb.1
  have hinner : (∑ a ∈ Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1),
      ((Real.log (a : ℝ) : ℝ) : ℂ) * ndPhaseExp T r (a * b))
      = ∑ a ∈ Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1),
          ((Real.log (a : ℝ) : ℂ) * ndExp T r a b) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [ndPhaseExp_mul]
  rw [norm_mul, hinner, thirdDerivativeFibreBound]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  by_cases hlt : (A - 1) / b + 1 < (B - 1) / b + 1
  · exact norm_sum_log_ndExp_third_le hT hr hb1 hlt (Nat.le_add_left 1 _) hspan hrA hlam
  · have hempty : Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1) = ∅ :=
      Finset.Ico_eq_empty (by omega)
    rw [hempty, Finset.sum_empty, norm_zero]
    have hlog : (0 : ℝ) ≤ Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ) := by
      rcases Nat.eq_zero_or_pos ((B - 1) / b + 1 - 1) with h | h
      · rw [h]
        simp
      · exact Real.log_nonneg (by exact_mod_cast h)
    have hfb : 0 ≤ thirdDerivativeTypeIBound T r b ((A - 1) / b + 1)
        ((B - 1) / b + 1) :=
      thirdDerivativeTypeIBound_nonneg hT hr hb1 (Nat.le_add_left 1 _)
    positivity

end

end RHTower.Sieve
