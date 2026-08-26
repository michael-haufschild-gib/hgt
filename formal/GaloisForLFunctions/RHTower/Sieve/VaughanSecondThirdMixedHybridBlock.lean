import GaloisForLFunctions.RHTower.Sieve.VonMangoldtBlockEstimateSecondThirdMixed
import GaloisForLFunctions.RHTower.Sieve.FibreSecondThirdMixedAggregate
import GaloisForLFunctions.RHTower.Sieve.ThirdDerivativeFibreConditions
import GaloisForLFunctions.RHTower.Sieve.TypeIIHybridPiece

/-!
# Vaughan block with mixed Type-I and hybrid Type-II estimates

This assembles the mixed derivative Type-I aggregate and unconditional hybrid correlation Type-II
bound.  Its remaining scalar conditions are exactly the crossover, curvature, and scale
inequalities later discharged in each prime-block regime.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction RHTower

noncomputable section

def secondThirdMixedVaughanTypeIEnvelope (T r : ℝ) (A B U V : ℕ) : ℝ :=
  Real.log (U * V) * secondThirdMixedAggregateEnvelope T r A B (U * V)
    + 2 * Real.log B * secondThirdMixedAggregateEnvelope T r A B V

def vaughanSecondThirdMixedHybridBlockEnvelope (C T r : ℝ) (A B L U V : ℕ) : ℝ :=
  secondThirdMixedVaughanTypeIEnvelope T r A B U V +
    typeIIHybridPieceEnvelope C T r A B L U V

theorem exists_norm_sum_vonMangoldt_ndPhaseExp_le_secondThird_mixed_hybrid :
    ∃ C : ℝ, 0 < C ∧ ∀ {T r : ℝ} {A B L U V : ℕ},
      0 < T → 0 < r → 1 ≤ A → A ≤ B → B ≤ 2 * A → B - 1 ≤ L →
      1 ≤ L → 1 ≤ U → 1 ≤ V → U < A → U * V ≤ A → U * V ≤ L → V ≤ L →
      8 * r ≤ (A : ℝ) →
      T * r * ((U * V : ℕ) : ℝ) ^ 3 ≤ 72 * Real.pi * (A : ℝ) ^ 4 →
      (∀ b ∈ Finset.Icc 1 (U * V),
        fibreKernel T r A ≤
            secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ)) →
          nearDiagonalLambda T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) →
      ‖∑ n ∈ Finset.Ico A B, ((vonMangoldt n : ℝ) : ℂ) * ndPhaseExp T r n‖
        ≤ vaughanSecondThirdMixedHybridBlockEnvelope C T r A B L U V := by
  obtain ⟨C, hC0, hII⟩ := exists_norm_typeII_piece_le_hybrid_vaughan
  refine ⟨C, hC0, ?_⟩
  intro T r A B L U V hT hr hA hAB hBA hBL hL hU hV hUA hUVA hUVL hVL h8 hcurv
    hsecondUV
  have hB : 1 ≤ B := le_trans hA hAB
  have hUV1 : 1 ≤ U * V := by simpa using Nat.mul_le_mul hU hV
  have hVUV : V ≤ U * V := by simpa [mul_comm] using Nat.mul_le_mul_left V hU
  have hVA : V ≤ A := le_trans hVUV hUVA
  have hthirdUV := thirdDerivative_fibre_conditions hT hr hA hAB hBA hUVA h8 hcurv
  have hcondUV : ∀ b ∈ Finset.Icc 1 (U * V),
      ((B - 1) / b + 1) - ((A - 1) / b + 1) - 1 ≤ ((A - 1) / b + 1)
        ∧ r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ)
        ∧ nearDiagonalLambda3 T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1
        ∧ (fibreKernel T r A ≤
            secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ)) →
          nearDiagonalLambda T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) := by
    intro b hb
    obtain ⟨hspan, hrA, hlam3⟩ := hthirdUV b hb
    exact ⟨hspan, hrA, hlam3, hsecondUV b hb⟩
  have hVpow : (V : ℝ) ^ 3 ≤ ((U * V : ℕ) : ℝ) ^ 3 := by
    have : (V : ℝ) ≤ ((U * V : ℕ) : ℝ) := by exact_mod_cast hVUV
    gcongr
  have hcurvV : T * r * (V : ℝ) ^ 3 ≤ 72 * Real.pi * (A : ℝ) ^ 4 :=
    le_trans (mul_le_mul_of_nonneg_left hVpow (by positivity)) hcurv
  have hthirdV := thirdDerivative_fibre_conditions hT hr hA hAB hBA hVA h8 hcurvV
  have hcondV : ∀ b ∈ Finset.Icc 1 V,
      ((B - 1) / b + 1) - ((A - 1) / b + 1) - 1 ≤ ((A - 1) / b + 1)
        ∧ r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ)
        ∧ nearDiagonalLambda3 T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1
        ∧ (fibreKernel T r A ≤
            secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ)) →
          nearDiagonalLambda T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) := by
    intro b hb
    obtain ⟨hspan, hrA, hlam3⟩ := hthirdV b hb
    have hbUV : b ∈ Finset.Icc 1 (U * V) := Finset.mem_Icc.2
      ⟨(Finset.mem_Icc.mp hb).1, le_trans (Finset.mem_Icc.mp hb).2 hVUV⟩
    exact ⟨hspan, hrA, hlam3, hsecondUV b hbUV⟩
  have hraw := norm_sum_vonMangoldt_ndPhaseExp_secondThird_mixed_le' hT hr hUA hA hB hBL
    hUVL hVL hcondUV hcondV
  have hI1 := sum_log_secondThirdMixedFibreBound_le hT hr hA hUV1 hUVA hAB hBA
  have hI2 := sum_two_secondThirdMixedFibreBound_log_le hT hr hA hVA hAB hBA
  have hIIbound := hII hT hr hA hB hL hBL hU hV h8
  rw [vaughanSecondThirdMixedHybridBlockEnvelope, secondThirdMixedVaughanTypeIEnvelope]
  push_cast at hI1
  linarith

end

end RHTower.Sieve
