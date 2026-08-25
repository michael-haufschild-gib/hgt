import GaloisForLFunctions.RHTower.Sieve.MollifiedTwistedDiagonalDirConvEnergy
import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorMollifiedCutoffError

/-!
# Exact full critical-detector diagonal energy

The zero-twist main diagonal for the unsmoothed critical detector times the literal linear
Levinson mollifier is exactly the full finite convolution square energy.
-/

noncomputable section

namespace RHTower

open Complex Finset

/-- Exact full-product diagonal energy of the finite critical detector and linear mollifier. -/
theorem mollifiedTwistedDiagonalIcc_levinsonCriticalDetector_zero_eq_energy
    (lam : ℝ) (L M : ℕ) :
    Sieve.mollifiedTwistedDiagonalIcc
        (Sieve.levinsonCriticalDetectorHeadCoeff lam)
        (Sieve.levinsonCriticalDetectorHeadCoeff lam)
        (Sieve.levinsonLinearMollifierCoeff M)
        (Sieve.levinsonLinearMollifierCoeff M) L M 0 =
      ∑ r : Fin (L * M),
        ((Complex.normSq
          (levinsonCriticalDetectorMollifiedFinCoeff lam L M r) : ℝ) : ℂ) := by
  rw [Sieve.mollifiedTwistedDiagonalIcc_zero_self_eq_sum_normSq_dirConv]
  apply Finset.sum_congr rfl
  intro r hr
  rfl

end RHTower
