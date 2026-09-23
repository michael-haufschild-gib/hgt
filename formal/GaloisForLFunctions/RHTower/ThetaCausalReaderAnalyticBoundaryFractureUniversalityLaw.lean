import GaloisForLFunctions.RHTower.XiThetaHeatNodeObstruction
import GaloisForLFunctions.RHTower.XiThetaSquareRateLaplace
import GaloisForLFunctions.RHTower.XiThetaSquareRateReflectedAction

/-!
# Theta causal-reader analytic-boundary fracture

The canonical square-rate theta reader has exact infinite Kronecker Laplace data in the causal
`L²` category and zero action on the reflected completed-theta half.  The same data cannot be the
values of a holomorphic symbol on a connected compactified heat domain because its nodes
accumulate at zero.
-/

namespace RHTower

open Complex MeasureTheory Set

noncomputable section

/-- A connected compactified holomorphic symbol cannot agree with all exact samples of the
canonical causal square-rate reader. -/
theorem no_analyticOnNhd_thetaHeatNode_of_agrees_with_causalReader
    {n : ℕ} (hn : 1 ≤ n)
    (F : ℂ → ℂ) {U : Set ℂ}
    (hU : IsPreconnected U)
    (hF : AnalyticOnNhd ℂ F U)
    (h0 : 0 ∈ U)
    (hnodes : ∀ m : ℕ, 1 ≤ m → (thetaHeatNode m : ℂ) ∈ U)
    (hagrees : ∀ m : ℕ, (hm : 1 ≤ m) →
      F (thetaHeatNode m) =
        causalLaplacePairing ((m : ℝ) ^ (2 : ℕ)) (sq_pos_of_pos (by positivity))
          (thetaHeatRateSourceReaderL2 n hn)) :
    False := by
  apply no_analyticOnNhd_thetaHeatNode_delta F hU hF h0 hnodes hn
  · rw [hagrees n hn,
      causalLaplacePairing_thetaHeatRateSourceReaderL2_kronecker hn hn]
    simp
  · intro m hm hmn
    rw [hagrees m hm,
      causalLaplacePairing_thetaHeatRateSourceReaderL2_kronecker hn hm]
    simp [hmn]

/-- No entire symbol can agree with all exact samples of the canonical causal square-rate
reader. -/
theorem no_entire_thetaHeatNode_of_agrees_with_causalReader
    {n : ℕ} (hn : 1 ≤ n)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hagrees : ∀ m : ℕ, (hm : 1 ≤ m) →
      F (thetaHeatNode m) =
        causalLaplacePairing ((m : ℝ) ^ (2 : ℕ)) (sq_pos_of_pos (by positivity))
          (thetaHeatRateSourceReaderL2 n hn)) :
    False := by
  apply no_entire_thetaHeatNode_delta F hF hn
  · rw [hagrees n hn,
      causalLaplacePairing_thetaHeatRateSourceReaderL2_kronecker hn hn]
    simp
  · intro m hm hmn
    rw [hagrees m hm,
      causalLaplacePairing_thetaHeatRateSourceReaderL2_kronecker hn hm]
    simp [hmn]

/-- **Theta causal-reader analytic-boundary fracture universality law.**  For every selected
positive square-rate index, the canonical causal reader has exact Kronecker samples, annihilates
the reflected theta half, and admits neither a connected compactified holomorphic realization nor
an entire realization of its complete sample data. -/
theorem thetaCausalReaderAnalyticBoundaryFractureUniversality
    {n : ℕ} (hn : 1 ≤ n) :
    (∀ m : ℕ, (hm : 1 ≤ m) →
      causalLaplacePairing ((m : ℝ) ^ (2 : ℕ)) (sq_pos_of_pos (by positivity))
          (thetaHeatRateSourceReaderL2 n hn) =
        if m = n then 1 else 0) ∧
      causalReaderReflectedThetaAction (thetaHeatRateSourceReaderL2 n hn) = 0 ∧
      (∀ (F : ℂ → ℂ) (U : Set ℂ),
        IsPreconnected U →
        AnalyticOnNhd ℂ F U →
        0 ∈ U →
        (∀ m : ℕ, 1 ≤ m → (thetaHeatNode m : ℂ) ∈ U) →
        (∀ m : ℕ, (hm : 1 ≤ m) →
          F (thetaHeatNode m) =
            causalLaplacePairing ((m : ℝ) ^ (2 : ℕ)) (sq_pos_of_pos (by positivity))
              (thetaHeatRateSourceReaderL2 n hn)) →
        False) ∧
      ∀ F : ℂ → ℂ,
        Differentiable ℂ F →
        (∀ m : ℕ, (hm : 1 ≤ m) →
          F (thetaHeatNode m) =
            causalLaplacePairing ((m : ℝ) ^ (2 : ℕ)) (sq_pos_of_pos (by positivity))
              (thetaHeatRateSourceReaderL2 n hn)) →
        False := by
  refine ⟨(fun m hm ↦
      causalLaplacePairing_thetaHeatRateSourceReaderL2_kronecker hn hm),
    thetaHeatRateSourceReaderL2_reflectedThetaAction_eq_zero hn, ?_, ?_⟩
  · intro F U hU hF h0 hnodes hagrees
    exact no_analyticOnNhd_thetaHeatNode_of_agrees_with_causalReader
      hn F hU hF h0 hnodes hagrees
  · intro F hF hagrees
    exact no_entire_thetaHeatNode_of_agrees_with_causalReader hn F hF hagrees

end

end RHTower
