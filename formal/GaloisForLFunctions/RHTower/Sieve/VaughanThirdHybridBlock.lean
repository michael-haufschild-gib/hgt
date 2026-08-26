import GaloisForLFunctions.RHTower.Sieve.VonMangoldtBlockEstimateThird
import GaloisForLFunctions.RHTower.Sieve.FibreThirdAggregate
import GaloisForLFunctions.RHTower.Sieve.ThirdDerivativeFibreConditions
import GaloisForLFunctions.RHTower.Sieve.TypeIIHybridPiece

/-!
# Complete third-derivative/hybrid Vaughan block estimate

The two Type I pieces use the `(1/6,2/3)` third-derivative envelope; the Type II piece uses the
unconditional `(1/2,1/2)` hybrid estimate.  All analytic conditions are discharged by explicit
scale inequalities.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction RHTower

noncomputable section

def thirdDerivativeVaughanTypeIEnvelope (T r : ℝ) (A B U V : ℕ) : ℝ :=
  Real.log (U * V) *
      (2 * thirdDerivativeFibreFirstCoefficient T r A * Real.sqrt (U * V)
        + 5 * thirdDerivativeFibreSecondCoefficient T r A)
    + 2 * Real.log B *
      (2 * thirdDerivativeFibreFirstCoefficient T r A * Real.sqrt V
        + 5 * thirdDerivativeFibreSecondCoefficient T r A)

def vaughanThirdHybridBlockEnvelope (C T r : ℝ) (A B L U V : ℕ) : ℝ :=
  thirdDerivativeVaughanTypeIEnvelope T r A B U V +
    typeIIHybridPieceEnvelope C T r A B L U V

/-- Closed prime block estimate with third-derivative Type I and hybrid Type II terms. -/
theorem exists_norm_sum_vonMangoldt_ndPhaseExp_le_third_hybrid :
    ∃ C : ℝ, 0 < C ∧ ∀ {T r : ℝ} {A B L U V : ℕ},
      0 < T → 0 < r → 1 ≤ A → A ≤ B → B ≤ 2 * A → B - 1 ≤ L →
      1 ≤ L → 1 ≤ U → 1 ≤ V → U < A → U * V ≤ A → U * V ≤ L → V ≤ L →
      8 * r ≤ (A : ℝ) →
      T * r * ((U * V : ℕ) : ℝ) ^ 3 ≤ 72 * Real.pi * (A : ℝ) ^ 4 →
      ‖∑ n ∈ Finset.Ico A B, ((vonMangoldt n : ℝ) : ℂ) * ndPhaseExp T r n‖
        ≤ vaughanThirdHybridBlockEnvelope C T r A B L U V := by
  obtain ⟨C, hC0, hII⟩ := exists_norm_typeII_piece_le_hybrid_vaughan
  refine ⟨C, hC0, ?_⟩
  intro T r A B L U V hT hr hA hAB hBA hBL hL hU hV hUA hUVA hUVL hVL h8 hcurv
  have hB : 1 ≤ B := le_trans hA hAB
  have hUV1 : 1 ≤ U * V := by
    simpa using Nat.mul_le_mul hU hV
  have hVUV : V ≤ U * V := by
    simpa [mul_comm] using Nat.mul_le_mul_left V hU
  have hVA : V ≤ A := le_trans hVUV hUVA
  have hcondUV := thirdDerivative_fibre_conditions hT hr hA hAB hBA hUVA h8 hcurv
  have hVpow : (V : ℝ) ^ 3 ≤ ((U * V : ℕ) : ℝ) ^ 3 := by
    have : (V : ℝ) ≤ ((U * V : ℕ) : ℝ) := by exact_mod_cast hVUV
    gcongr
  have hcurvV : T * r * (V : ℝ) ^ 3 ≤ 72 * Real.pi * (A : ℝ) ^ 4 :=
    le_trans (mul_le_mul_of_nonneg_left hVpow (by positivity)) hcurv
  have hcondV := thirdDerivative_fibre_conditions hT hr hA hAB hBA hVA h8 hcurvV
  have hraw := norm_sum_vonMangoldt_ndPhaseExp_third_le' hT hr hUA hA hB hBL
    hUVL hVL hcondUV hcondV
  have hI1 := sum_log_thirdDerivativeFibreBound_le hT hr hA hUV1 hUVA hAB hBA
  have hI2 := sum_two_thirdDerivativeFibreBound_log_le hT hr hA hVA hAB hBA
  have hIIbound := hII hT hr hA hB hL hBL hU hV h8
  rw [vaughanThirdHybridBlockEnvelope, thirdDerivativeVaughanTypeIEnvelope]
  push_cast at hI1
  linarith

end

end RHTower.Sieve
