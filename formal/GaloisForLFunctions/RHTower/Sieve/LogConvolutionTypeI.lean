import GaloisForLFunctions.RHTower.Sieve.ZetaConvolutionTypeI

/-!
# A `log`-convolution over a block is a type-I sum with a logarithmic weight

The second Vaughan piece is `log ∗ μ_V`.  It has the same fibre structure as the first, except
that the inner sum carries the weight `log a`, which Abel's inequality removes at the cost of a
factor `2 log` of the right endpoint of the fibre.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

/-- **The `log`-convolution type-I estimate.** -/
theorem norm_sum_log_conv_ndPhaseExp_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {A B L : ℕ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L) (g : ℕ → ℂ)
    (hcond : ∀ b ∈ Finset.Icc 1 L,
      r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ)
        ∧ nearDiagonalLambda T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) :
    ‖∑ n ∈ Finset.Ico A B,
        (∑ p ∈ n.divisorsAntidiagonal, ((Real.log (p.1 : ℝ) : ℝ) : ℂ) * g p.2)
          * ndPhaseExp T r n‖
      ≤ ∑ b ∈ Finset.Icc 1 L,
          ‖g b‖ * (2 * fibreBound T r A B b
            * Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ)) := by
  rw [sum_conv_mul_Ico_eq hA hB hBL (fun a => ((Real.log (a : ℝ) : ℝ) : ℂ)) g (ndPhaseExp T r)]
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
