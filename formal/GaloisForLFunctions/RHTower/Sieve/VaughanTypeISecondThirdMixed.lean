import GaloisForLFunctions.RHTower.Sieve.FibreSecondThirdMixed

/-!
# Vaughan Type-I pieces with mixed derivative tests

Every coefficient-supported fibre uses the second-derivative test below the exact crossover and
the sharp third-derivative test above it.  Both ordinary and logarithmically weighted convolution
forms are retained for Vaughan's identity.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

theorem norm_sum_log_ndExp_secondThird_mixed_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B b : ℕ} (hb : 1 ≤ b)
    (hlt : (A - 1) / b + 1 < (B - 1) / b + 1)
    (hspan : ((B - 1) / b + 1) - ((A - 1) / b + 1) - 1 ≤ ((A - 1) / b + 1))
    (hrA : r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ))
    (hlam3 : nearDiagonalLambda3 T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1)
    (hlam2 : fibreKernel T r A ≤
        secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ)) →
      nearDiagonalLambda T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) :
    ‖∑ k ∈ Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1),
        ((Real.log k : ℝ) : ℂ) * ndExp T r k b‖
      ≤ 2 * secondThirdMixedFibreBound T r A B b *
          Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ) := by
  rw [secondThirdMixedFibreBound]
  split_ifs with hlow
  · rw [fibreBound]
    exact norm_sum_log_ndExp_le hT hr hb hlt (Nat.le_add_left 1 _) hrA (hlam2 hlow)
  · rw [sharpThirdDerivativeFibreBound]
    exact norm_sum_log_ndExp_third_sharp_le hT hr hb hlt (Nat.le_add_left 1 _)
      hspan hrA hlam3

theorem norm_sum_zeta_conv_ndPhaseExp_secondThird_mixed_le' {T r : ℝ}
    (hT : 0 < T) (hr : 0 < r) {A B L K : ℕ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L) (hKL : K ≤ L) (g : ℕ → ℂ)
    (hsupp : ∀ b, K < b → g b = 0)
    (hcond : ∀ b ∈ Finset.Icc 1 K,
      ((B - 1) / b + 1) - ((A - 1) / b + 1) - 1 ≤ ((A - 1) / b + 1)
        ∧ r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ)
        ∧ nearDiagonalLambda3 T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1
        ∧ (fibreKernel T r A ≤
            secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ)) →
          nearDiagonalLambda T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1)) :
    ‖∑ n ∈ Finset.Ico A B,
        (∑ p ∈ n.divisorsAntidiagonal, (1 : ℂ) * g p.2) * ndPhaseExp T r n‖
      ≤ ∑ b ∈ Finset.Icc 1 K, ‖g b‖ * secondThirdMixedFibreBound T r A B b := by
  rw [sum_conv_mul_Ico_eq hA hB hBL (fun _ => (1 : ℂ)) g (ndPhaseExp T r),
    sum_Icc_restrict_of_support hKL g _ hsupp]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun b hb => ?_
  rw [Finset.mem_Icc] at hb
  obtain ⟨hspan, hrA, hlam3, hlam2⟩ := hcond b (Finset.mem_Icc.2 hb)
  have hinner : (∑ a ∈ Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1),
      (1 : ℂ) * ndPhaseExp T r (a * b)) =
      ∑ a ∈ Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1), ndExp T r a b := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [one_mul, ndPhaseExp_mul]
  rw [norm_mul, hinner]
  exact mul_le_mul_of_nonneg_left
    (norm_sum_ndExp_secondThird_mixed_le hT hr hb.1 hspan hrA hlam3 hlam2)
    (norm_nonneg _)

theorem norm_sum_log_conv_ndPhaseExp_secondThird_mixed_le' {T r : ℝ}
    (hT : 0 < T) (hr : 0 < r) {A B L K : ℕ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L) (hKL : K ≤ L) (g : ℕ → ℂ)
    (hsupp : ∀ b, K < b → g b = 0)
    (hcond : ∀ b ∈ Finset.Icc 1 K,
      ((B - 1) / b + 1) - ((A - 1) / b + 1) - 1 ≤ ((A - 1) / b + 1)
        ∧ r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ)
        ∧ nearDiagonalLambda3 T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1
        ∧ (fibreKernel T r A ≤
            secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ)) →
          nearDiagonalLambda T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1)) :
    ‖∑ n ∈ Finset.Ico A B,
        (∑ p ∈ n.divisorsAntidiagonal, ((Real.log (p.1 : ℝ) : ℝ) : ℂ) * g p.2)
          * ndPhaseExp T r n‖
      ≤ ∑ b ∈ Finset.Icc 1 K, ‖g b‖ *
          (2 * secondThirdMixedFibreBound T r A B b *
            Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ)) := by
  rw [sum_conv_mul_Ico_eq hA hB hBL (fun a => ((Real.log (a : ℝ) : ℝ) : ℂ)) g
      (ndPhaseExp T r), sum_Icc_restrict_of_support hKL g _ hsupp]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun b hb => ?_
  rw [Finset.mem_Icc] at hb
  obtain ⟨hspan, hrA, hlam3, hlam2⟩ := hcond b (Finset.mem_Icc.2 hb)
  have hinner : (∑ a ∈ Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1),
      ((Real.log (a : ℝ) : ℝ) : ℂ) * ndPhaseExp T r (a * b)) =
      ∑ a ∈ Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1),
          ((Real.log (a : ℝ) : ℂ) * ndExp T r a b) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ndPhaseExp_mul]
  rw [norm_mul, hinner]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  by_cases hlt : (A - 1) / b + 1 < (B - 1) / b + 1
  · exact norm_sum_log_ndExp_secondThird_mixed_le hT hr hb.1 hlt hspan hrA hlam3 hlam2
  · have hempty : Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1) = ∅ :=
      Finset.Ico_eq_empty (by omega)
    rw [hempty, Finset.sum_empty, norm_zero]
    have hlog : 0 ≤ Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ) := by
      rcases Nat.eq_zero_or_pos ((B - 1) / b + 1 - 1) with h | h
      · rw [h]
        simp
      · exact Real.log_nonneg (by exact_mod_cast h)
    have hfb := secondThirdMixedFibreBound_nonneg (A := A) (B := B) hT hr hb.1
    positivity

end

end RHTower.Sieve
