import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalCentering

namespace GaloisForLFunctions.HTGeometry

open QuantumAlg
noncomputable section

/-- The zeroth Fourier coordinate is exactly the normalized total mass. -/
theorem egbFixedChargeACriticalFourierCoordinates_zero_frequency (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℂ) :
    egbFixedChargeACriticalFourierCoordinates n f 0 = invSqrtN (n + 3) * ∑ i, f i := by
  change (∑ j, star (QFTMatrix (n + 3) j 0) * f j) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [QFT_entry, Fin.val_zero, Nat.mul_zero, pow_zero, mul_one, star_invSqrtN]

/-- A centered real input has no invariant Fourier component. -/
theorem egbFixedChargeACriticalCenteredProfile_zero_frequency (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeACriticalFourierCoordinates n
      (fun i => (egbFixedChargeACriticalCenteredProfile n f i : ℂ)) 0 = 0 := by
  rw [egbFixedChargeACriticalFourierCoordinates_zero_frequency, ← Complex.ofReal_sum,
    egbFixedChargeACriticalCenteredProfile_mass_zero, Complex.ofReal_zero, mul_zero]

end
end GaloisForLFunctions.HTGeometry
