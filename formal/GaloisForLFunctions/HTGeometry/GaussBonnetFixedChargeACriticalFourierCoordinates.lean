import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsHiddenEntropy

namespace GaloisForLFunctions.HTGeometry

open QuantumAlg
open scoped Matrix
noncomputable section

/-- The actual corpus QFT analysis coordinates for a critical-grid input. -/
def egbFixedChargeACriticalFourierCoordinates (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℂ) : Fin (2 ^ (n + 3)) → ℂ :=
  star (QFTMatrix (n + 3)) *ᵥ f

/-- The full QFT coordinates reconstruct every input exactly. -/
theorem egbFixedChargeACriticalFourierCoordinates_inverse (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℂ) :
    QFTMatrix (n + 3) *ᵥ egbFixedChargeACriticalFourierCoordinates n f = f := by
  unfold egbFixedChargeACriticalFourierCoordinates
  have hu := Matrix.mem_unitaryGroup_iff.mp (QFT_mem_unitaryGroup (n + 3))
  rw [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]

/-- No information is lost by merely changing to the full Fourier coordinates. -/
theorem egbFixedChargeACriticalFourierCoordinates_injective (n : ℕ) :
    Function.Injective (egbFixedChargeACriticalFourierCoordinates n) := by
  intro f g h
  calc
    f = QFTMatrix (n + 3) *ᵥ egbFixedChargeACriticalFourierCoordinates n f :=
      (egbFixedChargeACriticalFourierCoordinates_inverse n f).symm
    _ = QFTMatrix (n + 3) *ᵥ egbFixedChargeACriticalFourierCoordinates n g := by rw [h]
    _ = g := egbFixedChargeACriticalFourierCoordinates_inverse n g

/-- Every Fourier coordinate of an evolved input is its original coordinate times an exact multiplier. -/
theorem egbFixedChargeACriticalFourierCoordinates_evolution (n m : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℂ) :
    egbFixedChargeACriticalFourierCoordinates n ((egbFixedChargeACriticalMarkovMatrix n ^ m) *ᵥ f) =
      fun j => egbFixedChargeAFiveModeSpectrum n egbFixedChargeACriticalMarkovEigenvalues j ^ m *
        egbFixedChargeACriticalFourierCoordinates n f j := by
  unfold egbFixedChargeACriticalFourierCoordinates
  have hu := Matrix.mem_unitaryGroup_iff'.mp (QFT_mem_unitaryGroup (n + 3))
  rw [Matrix.mulVec_mulVec, egbFixedChargeACriticalMarkovMatrix_QFT,
    egbFixedChargeAQFTMultiplier_pow, egbFixedChargeAQFTMultiplier,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, hu, Matrix.one_mul,
    ← Matrix.mulVec_mulVec]
  funext j
  exact Matrix.mulVec_diagonal _ _ _

end
end GaloisForLFunctions.HTGeometry
