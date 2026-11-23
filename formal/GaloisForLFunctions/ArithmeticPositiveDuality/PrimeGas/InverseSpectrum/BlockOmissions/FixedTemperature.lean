import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.BlockOmissions.BlockClosure
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.BlockOmissions.BlockResponse
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockStability.BornBounds

/-! # The optimal amplitude-to-probability factor at each fixed temperature -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

/-- At any fixed positive inverse temperature the exact physical comparison factor is the missing dimension. -/
theorem fixed_temperature_born_factor_iff (r : ℕ) (β : GibbsExponent) (K : ℝ) :
    (∀ (P Q : Projection) (hP : MissingDimension P (r+1)) (cP : Conserving (projected P))
      (hQ : MissingDimension Q (r+1)) (cQ : Conserving (projected Q)),
      detectorError (powerResponse β) (physicalSpectrum P hP cP) (physicalSpectrum Q hQ cQ)^2 ≤
      K * detectorError (powerResponse (doubleExponent β)) (physicalSpectrum P hP cP) (physicalSpectrum Q hQ cQ)) ↔
      ((r+1 : ℕ):ℝ) ≤ K := by
  constructor
  · intro h
    have hn (N : ℕ) : normalizedBlock β (r+1) N ^ 2 ≤ K * normalizedBlock (doubleExponent β) (r+1) N := by
      have he := hot_block_mem_closed_of_physical r N (isClosed_le ((continuous_detectorError (powerResponse β) (r+1)).pow 2)
        (continuous_const.mul (continuous_detectorError (powerResponse (doubleExponent β)) (r+1)))) (by
          rintro _ ⟨P,hP,cP,rfl⟩ _ ⟨Q,hQ,cQ,rfl⟩
          exact h P Q hP cP hQ cQ)
      change detectorError (powerResponse β) (hotEdge (r+1)) (blockSpectrum N (r+1))^2 ≤
        K * detectorError (powerResponse (doubleExponent β)) (hotEdge (r+1)) (blockSpectrum N (r+1)) at he
      simp only [detectorError_block,power_tailCeiling_eq_scaled,mul_pow] at he
      rw [power_doubleExponent β (occupationWeight_pos N).le,mul_left_comm K] at he
      exact le_of_mul_le_mul_left he (sq_pos_of_pos (Real.rpow_pos_of_pos (occupationWeight_pos N) β.val))
    have hb := le_of_tendsto_of_tendsto ((normalizedBlock_tendsto β (r+1)).pow 2)
      ((normalizedBlock_tendsto (doubleExponent β) (r+1)).const_mul K) (Eventually.of_forall hn)
    rw [pow_two] at hb
    exact le_of_mul_le_mul_right hb (Nat.cast_pos.mpr (Nat.succ_pos r))
  · intro h P Q hP cP hQ cQ
    exact (amplitude_sq_le_rank_mul_born β _ _).trans (mul_le_mul_of_nonneg_right h (detectorError_nonneg _ _ _))

#print axioms fixed_temperature_born_factor_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
