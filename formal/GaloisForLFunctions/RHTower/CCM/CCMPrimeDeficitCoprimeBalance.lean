import GaloisForLFunctions.RHTower.LogarithmicCoprimeEnergy
import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitMobiusCenteredEnergy

/-!
# Bounded signed coprime balance for the actual prime deficit

The bounded dilation source controls a complete coprime quadratic form of
its Möbius reconstruction. Restoring the explicit main terms gives an
exact balance for the full critical deficit energy. The compensating
coprime cross work remains signed; its lower bound is not assumed.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

def ccmPrimeDeficitCoprimeSquareSource (T : ℝ) : ℝ :=
  Real.exp (-T) * logarithmicMobiusInverse
    (fun t => ccmPrimeDeficitDilationRemainder t ^ 2) T

def ccmPrimeDeficitCoprimeCrossWork (T : ℝ) : ℝ :=
  Real.exp (-T) *
    (logarithmicCoprimeCross ccmPrimeDeficitMobiusCenteredWork T -
      ccmPrimeDeficitMobiusExplicitWork T ^ 2 -
        2 * ccmPrimeDeficitMobiusExplicitWork T * ccmPrimeDeficitMobiusCenteredWork T)

theorem logarithmicDilationSum_ccmPrimeDeficitMobiusCenteredWork {T : ℝ} (hT : 0 ≤ T) :
    logarithmicDilationSum ccmPrimeDeficitMobiusCenteredWork T =
      ccmPrimeDeficitDilationRemainder T := by
  exact logarithmicDilationSum_mobiusInverse ccmPrimeDeficitDilationRemainder hT

/-- The actual centered inverse satisfies the complete signed coprime
identity, including every delayed pair and its original endpoint. -/
theorem logarithmicCoprimeEnergy_ccmPrimeDeficitMobiusCenteredWork (T : ℝ) :
    logarithmicCoprimeEnergy ccmPrimeDeficitMobiusCenteredWork T =
      logarithmicMobiusInverse (fun t => ccmPrimeDeficitDilationRemainder t ^ 2) T := by
  exact logarithmicCoprimeEnergy_mobiusInverse ccmPrimeDeficitDilationRemainder T

private theorem abs_moebiusCoeff_eq_sq (n : ℕ) :
    |moebiusCoeff n| = moebiusCoeff n ^ 2 := by
  have h : |ArithmeticFunction.moebius n| = ArithmeticFunction.moebius n ^ 2 := by
    rw [ArithmeticFunction.abs_moebius, ArithmeticFunction.moebius_sq]
  unfold moebiusCoeff
  exact_mod_cast h

/-- Cancellation of common divisors turns the old diagonal budget into
a bound for the complete signed coprime correlation. -/
theorem abs_ccmPrimeDeficitCoprimeSquareSource_le_diagonal (T : ℝ) :
    |ccmPrimeDeficitCoprimeSquareSource T| ≤ ccmPrimeDeficitMobiusCenteredDiagonal T := by
  rw [ccmPrimeDeficitCoprimeSquareSource, abs_mul, abs_of_pos (Real.exp_pos (-T))]
  unfold logarithmicMobiusInverse logarithmicWeightedDilation ccmPrimeDeficitMobiusCenteredDiagonal
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos (-T)).le
  refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro n _
  change |moebiusCoeff n * ccmPrimeDeficitDilationRemainder (T - Real.log n) ^ 2| = _
  rw [abs_mul, abs_moebiusCoeff_eq_sq, abs_of_nonneg (sq_nonneg _), mul_pow]

theorem abs_ccmPrimeDeficitCoprimeSquareSource_le (T : ℝ) :
    |ccmPrimeDeficitCoprimeSquareSource T| ≤ 49 / 4 :=
  (abs_ccmPrimeDeficitCoprimeSquareSource_le_diagonal T).trans
    (ccmPrimeDeficitMobiusCenteredDiagonal_le T)

/-- Exact balance for the full deficit, with all explicit/centered mixed
terms restored. The surviving signed work couples coprime histories. -/
theorem ccmPrimeDeficitCriticalEnergy_add_coprimeCrossWork {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitCriticalEnergy T + ccmPrimeDeficitCoprimeCrossWork T =
      ccmPrimeDeficitCoprimeSquareSource T := by
  have h := logarithmicCoprimeEnergy_ccmPrimeDeficitMobiusCenteredWork T
  rw [logarithmicCoprimeEnergy_eq_endpoint_add_cross _ hT] at h
  rw [ccmPrimeDeficitCriticalEnergy, ccmLogChebyshevDeficitPrimitive_eq_moebius_centered_work hT,
    ccmPrimeDeficitCoprimeCrossWork, ccmPrimeDeficitCoprimeSquareSource, ← h]
  ring

/-- Uniform control of the complete arithmetic balance, retaining the
full deficit energy and every signed coprime cross term. -/
theorem abs_ccmPrimeDeficitCriticalEnergy_add_coprimeCrossWork_le {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitCriticalEnergy T + ccmPrimeDeficitCoprimeCrossWork T| ≤ 49 / 4 := by
  rw [ccmPrimeDeficitCriticalEnergy_add_coprimeCrossWork hT]
  exact abs_ccmPrimeDeficitCoprimeSquareSource_le T

end RHTower
