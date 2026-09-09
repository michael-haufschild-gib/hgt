import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalFourierCoordinates

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix
noncomputable section

/-- Two inputs have identical evolved outputs precisely when their five retained Fourier coordinates agree. -/
theorem egbFixedChargeACriticalMarkovMatrix_fiber_iff (n m : ℕ)
    (f g : Fin (2 ^ (n + 3)) → ℂ) :
    (egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) *ᵥ f =
      (egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) *ᵥ g ↔
        ∀ k : Fin 5, egbFixedChargeACriticalFourierCoordinates n f (egbFixedChargeAFiveFourierModes n k) =
          egbFixedChargeACriticalFourierCoordinates n g (egbFixedChargeAFiveFourierModes n k) := by
  rw [← (egbFixedChargeACriticalFourierCoordinates_injective n).eq_iff,
    egbFixedChargeACriticalFourierCoordinates_evolution,
    egbFixedChargeACriticalFourierCoordinates_evolution]
  constructor
  · intro h k
    have he := congrFun h (egbFixedChargeAFiveFourierModes n k)
    have hw : egbFixedChargeAFiveModeSpectrum n egbFixedChargeACriticalMarkovEigenvalues
        (egbFixedChargeAFiveFourierModes n k) ≠ 0 := by
      intro hz
      exact (egbFixedChargeACriticalMarkovSpectrum_zero_iff n _).mp hz ⟨k, rfl⟩
    exact mul_left_cancel₀ (pow_ne_zero (m + 1) hw) he
  · intro h
    funext j
    by_cases hj : ∃ k : Fin 5, j = egbFixedChargeAFiveFourierModes n k
    · obtain ⟨k, rfl⟩ := hj
      rw [h k]
    · have hz := (egbFixedChargeACriticalMarkovSpectrum_zero_iff n j).mpr hj
      simp [hz]

/-- The complete nullspace consists exactly of inputs with all five retained coordinates zero. -/
theorem egbFixedChargeACriticalMarkovMatrix_nullspace_iff (n m : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℂ) :
    (egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) *ᵥ f = 0 ↔
      ∀ k : Fin 5, egbFixedChargeACriticalFourierCoordinates n f
        (egbFixedChargeAFiveFourierModes n k) = 0 := by
  simpa only [Matrix.mulVec_zero, egbFixedChargeACriticalFourierCoordinates, Pi.zero_apply] using
    egbFixedChargeACriticalMarkovMatrix_fiber_iff n m f 0

/-- All exact coalescence occurs at the first transition; later finite times identify no new input pairs. -/
theorem egbFixedChargeACriticalMarkovMatrix_fiber_time_independent (n m : ℕ)
    (f g : Fin (2 ^ (n + 3)) → ℂ) :
    (egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) *ᵥ f =
      (egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) *ᵥ g ↔
        egbFixedChargeACriticalMarkovMatrix n *ᵥ f = egbFixedChargeACriticalMarkovMatrix n *ᵥ g := by
  have h := (egbFixedChargeACriticalMarkovMatrix_fiber_iff n m f g).trans
    (egbFixedChargeACriticalMarkovMatrix_fiber_iff n 0 f g).symm
  simpa only [Nat.zero_add, pow_one] using h

end
end GaloisForLFunctions.HTGeometry
