import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSpikeProbability
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFourierObservability

/-! # Exact full Fourier coordinates of the positive spike Gibbs law -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open QuantumAlg
open scoped Matrix

private theorem qft_zero_column (n : ℕ) (i : Fin (2 ^ (n + 3))) :
    QFTMatrix (n + 3) i 0 = invSqrtN (n + 3) := by
  rw [QFT_entry]
  simp

private theorem coordinate_zero_column (n : ℕ) :
    egbFixedChargeACriticalFourierCoordinates n ((QFTMatrix (n + 3)).col 0) =
      Pi.single 0 (1 : ℂ) := by
  unfold egbFixedChargeACriticalFourierCoordinates
  have hu := Matrix.mem_unitaryGroup_iff'.mp (QFT_mem_unitaryGroup (n + 3))
  rw [← Matrix.mulVec_single_one (QFTMatrix (n + 3)) 0,
    Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]

private theorem coordinate_delta_zero (n : ℕ) (k : Fin (2 ^ (n + 3))) :
    egbFixedChargeACriticalFourierCoordinates n (Pi.single 0 (1 : ℂ)) k =
      invSqrtN (n + 3) := by
  unfold egbFixedChargeACriticalFourierCoordinates
  rw [Matrix.mulVec_single_one]
  change star (QFTMatrix (n + 3)) k 0 = _
  rw [Matrix.star_apply, QFT_entry]
  simp

/-- The real spike probability is an exact linear combination of the zero QFT column and the zero coordinate vector. -/
theorem egbFixedChargeAGibbsSpikeProbability_QFT_decomposition (n : ℕ) :
    (fun i => (egbFixedChargeAGibbsSpikeProbability n i : ℂ)) =
      (invSqrtN (n + 3) / 2) • (QFTMatrix (n + 3)).col 0 +
        (1 / 2 : ℂ) • Pi.single 0 1 := by
  funext i
  change (egbFixedChargeAGibbsSpikeProbability n i : ℂ) =
    (invSqrtN (n + 3) / 2) * QFTMatrix (n + 3) i 0 + (1 / 2 : ℂ) * ((Pi.single 0 1 : Fin (2 ^ (n + 3)) → ℂ) i)
  rw [qft_zero_column]
  have hn : invSqrtN (n + 3) / 2 * invSqrtN (n + 3) = ((↑((2 : ℝ) ^ (n + 3)) : ℂ))⁻¹ / 2 := by
    calc
      _ = (invSqrtN (n + 3) * invSqrtN (n + 3)) / 2 := by ring
      _ = _ := by rw [invSqrtN_mul_self]
  rw [hn]
  by_cases hi : i = 0
  · simp [egbFixedChargeAGibbsSpikeProbability, hi]
  · simp [egbFixedChargeAGibbsSpikeProbability, hi]

/-- Every full Fourier coordinate is explicit, including all modes annihilated by the thermal kernel. -/
theorem egbFixedChargeAGibbsSpike_fourier_coordinates (n : ℕ) (k : Fin (2 ^ (n + 3))) :
    egbFixedChargeACriticalFourierCoordinates n
      (fun i => (_root_.HTGeometry.finiteGibbsStateWeight 1 (egbFixedChargeAGibbsSpikeEnergy n) i : ℂ)) k =
      if k = 0 then invSqrtN (n + 3) else invSqrtN (n + 3) / 2 := by
  rw [egbFixedChargeAGibbsSpike_realization, egbFixedChargeAGibbsSpikeProbability_QFT_decomposition]
  change (star (QFTMatrix (n + 3)) *ᵥ
    ((invSqrtN (n + 3) / 2) • (QFTMatrix (n + 3)).col 0 + (1 / 2 : ℂ) • Pi.single 0 1)) k = _
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  change (invSqrtN (n + 3) / 2) *
      egbFixedChargeACriticalFourierCoordinates n ((QFTMatrix (n + 3)).col 0) k +
    (1 / 2 : ℂ) * egbFixedChargeACriticalFourierCoordinates n (Pi.single 0 1) k = _
  rw [coordinate_zero_column, coordinate_delta_zero]
  by_cases hk : k = 0 <;> simp [hk] <;> ring

/-- The five retained Gibbs moments have the same explicit nonzero amplitude in every nonconstant sector. -/
theorem egbFixedChargeAGibbsSpike_fourier_moments (n : ℕ) (k : Fin 5) :
    egbFixedChargeAGibbsFourierMoment n 1 (egbFixedChargeAGibbsSpikeEnergy n) k =
      if k = 0 then invSqrtN (n + 3) else invSqrtN (n + 3) / 2 := by
  unfold egbFixedChargeAGibbsFourierMoment
  rw [egbFixedChargeAGibbsSpike_fourier_coordinates]
  have hzero : egbFixedChargeAFiveFourierModes n 0 = 0 := rfl
  by_cases hk : k = 0
  · rw [hk, hzero]
    simp
  · have hn : egbFixedChargeAFiveFourierModes n k ≠ 0 := by
      intro h
      exact hk (egbFixedChargeAFiveFourierModes_injective n (h.trans hzero.symm))
    simp only [if_neg hk, if_neg hn]

end
end GaloisForLFunctions.HTGeometry
