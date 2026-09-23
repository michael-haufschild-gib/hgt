import GaloisForLFunctions.RHTower.Sieve.LinearMeanSquareCapstone
import GaloisForLFunctions.RHTower.Sieve.LogPolyMoebius
import GaloisForLFunctions.RHTower.Sieve.MoebiusEulerDamping

/-!
# The Möbius short-interval mean square over a range

Instantiating the linear capstone at the Möbius coefficients.  The frequency-restricted bound `M₁` is
supplied by the twisted Möbius sum, through the identity of `LogPolyMoebius.lean`, and the global
bound `M₂` is the trivial `(#s)²`:

    ∫_Y^{Y(1+ε)^K} |∑_{x < n ≤ x+L} μ(n)|² dx
      ≤ Y(1+ε)^K · K · ( 2(M₁·log(1+L/Y) + (#s)²·2/(π²W)) + 2(εL+1)²·log(1+ε) ) .

Only the frequency-restricted bound carries arithmetic; everything else is elementary.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Finset

/-- The trivial bound on the Möbius Dirichlet polynomial. -/
theorem normSq_logPoly_moebiusC_le (s : Finset ℕ) (w : ℝ) :
    ‖logPoly moebiusC s w‖ ^ (2 : ℕ) ≤ ((s.card : ℝ)) ^ (2 : ℕ) := by
  have hbd : ‖logPoly moebiusC s w‖ ≤ (s.card : ℝ) := by
    rw [logPoly]
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ 1 fun n _ => ?_) ?_
    · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact norm_moebiusC_le_one n
    · rw [nsmul_eq_mul, mul_one]
  have h0 : (0 : ℝ) ≤ ‖logPoly moebiusC s w‖ := norm_nonneg _
  nlinarith [hbd, h0]

/-- **The Möbius short-interval mean square over a range.** -/
theorem integral_Ioc_normSq_moebius_range_le (s : Finset ℕ) (hs : ∀ n ∈ s, 0 < n)
    {L Y ε M₁ W : ℝ} (hL : 0 < L) (hY : 0 < Y) (hε : 0 ≤ ε) (hW : 0 < W) (hM₁ : 0 ≤ M₁)
    (h₁ : ∀ w : ℝ, |w| ≤ W →
      ‖∑ n ∈ s, moebiusTwist (-(2 * Real.pi * w)) n‖ ^ (2 : ℕ) ≤ M₁) (K : ℕ) :
    (∫ x in Set.Ioc Y (Y * (1 + ε) ^ K), ‖linSum moebiusC s L x‖ ^ (2 : ℕ))
      ≤ (Y * (1 + ε) ^ K)
          * ((K : ℝ) * blockCost L Y ε M₁ (((s.card : ℝ)) ^ (2 : ℕ)) W) := by
  refine integral_Ioc_normSq_linSum_range_le moebiusC s hs norm_moebiusC_le_one hL hY hε hW hM₁
    (by positivity) ?_ (fun w => normSq_logPoly_moebiusC_le s w) K
  intro w hw
  rw [Set.mem_Icc] at hw
  have habs : |w| ≤ W := abs_le.2 ⟨hw.1, hw.2⟩
  have hpoly : logPoly moebiusC s w = ∑ n ∈ s, moebiusTwist (-(2 * Real.pi * w)) n := by
    exact logPoly_moebius_eq s w
  rw [hpoly]
  exact h₁ w habs

end RHTower.Sieve
