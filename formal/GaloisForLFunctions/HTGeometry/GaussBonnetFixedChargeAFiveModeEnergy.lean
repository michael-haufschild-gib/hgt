import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAQFTParseval

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix
noncomputable section

/-- The energy of any five-mode multiplier is an exact sum over its five distinct coordinates. -/
theorem egbFixedChargeAFiveModeSpectrum_energy (n : ℕ) (a : Fin 5 → ℝ)
    (f : Fin (2 ^ (n + 3)) → ℂ) :
    ∑ j, ‖egbFixedChargeAFiveModeSpectrum n a j * f j‖ ^ (2 : ℕ) =
      ∑ k : Fin 5, (a k) ^ (2 : ℕ) * ‖f (egbFixedChargeAFiveFourierModes n k)‖ ^ (2 : ℕ) := by
  classical
  have hp (j : Fin (2 ^ (n + 3))) :
      ‖egbFixedChargeAFiveModeSpectrum n a j * f j‖ ^ (2 : ℕ) =
        ∑ k : Fin 5, if egbFixedChargeAFiveFourierModes n k = j then
          (a k) ^ (2 : ℕ) * ‖f j‖ ^ (2 : ℕ) else 0 := by
    by_cases hj : ∃ k : Fin 5, j = egbFixedChargeAFiveFourierModes n k
    · obtain ⟨k, rfl⟩ := hj
      simp [egbFixedChargeAFiveModeSpectrum_mode,
        (egbFixedChargeAFiveFourierModes_injective n).eq_iff,
        norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    · have hn : ∀ k : Fin 5, egbFixedChargeAFiveFourierModes n k ≠ j := by
        intro k hk
        exact hj ⟨k, hk.symm⟩
      have hz : egbFixedChargeAFiveModeSpectrum n a j = 0 := by
        simp [egbFixedChargeAFiveModeSpectrum, hn]
      simp [hz, hn]
  simp_rw [hp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp

/-- Every positive transition power has a five-term exact energy decomposition. -/
theorem egbFixedChargeACriticalMarkovMatrix_five_mode_energy (n m : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℂ) :
    ∑ i, ‖((egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) *ᵥ f) i‖ ^ (2 : ℕ) =
      ∑ k : Fin 5, (egbFixedChargeACriticalMarkovEigenvalues k ^ (m + 1)) ^ (2 : ℕ) *
        ‖egbFixedChargeACriticalFourierCoordinates n f (egbFixedChargeAFiveFourierModes n k)‖ ^ (2 : ℕ) := by
  rw [egbFixedChargeACriticalMarkovMatrix_spectral_energy]
  simp_rw [egbFixedChargeAFiveModeSpectrum_pow]
  exact egbFixedChargeAFiveModeSpectrum_energy n _ _

end
end GaloisForLFunctions.HTGeometry
