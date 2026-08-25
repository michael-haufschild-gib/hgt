import GaloisForLFunctions.RHTower.Sieve.DirichletYoung
import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorLongEnergyDivisorBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorMollifiedCutoffError

/-!
# Divisor-free Young bounds for the critical-detector long energy

Finite multiplicative Young gives a complementary unconditional long-energy cap without a divisor
factor.  It is deliberately recorded as a coarse polynomial envelope, not as the sharp Levinson
tail asymptotic.
-/

noncomputable section

namespace RHTower

open Complex Finset

/-- Divisor-free `ell^2`--`ell^1` cap for the exact long convolution energy. -/
theorem levinsonCriticalDetectorLongEnergy_le_l2_l1
    (lam : ℝ) (L M : ℕ) :
    levinsonCriticalDetectorLongEnergy lam L M ≤
      (∑ n : Fin L,
          ‖Sieve.levinsonCriticalDetectorHeadCoeff lam ((n : ℕ) + 1)‖ ^ 2) *
        (∑ m : Fin M, ‖levinsonLinearMollifierFinCoeff M m‖) ^ 2 := by
  refine (levinsonCriticalDetectorLongEnergy_le_fullEnergy lam L M).trans ?_
  simpa only [levinsonCriticalDetectorMollifiedFinCoeff] using
    Sieve.sum_norm_sq_dirConv_le_l2_l1 L M
      (fun n : Fin L => Sieve.levinsonCriticalDetectorHeadCoeff lam ((n : ℕ) + 1))
      (levinsonLinearMollifierFinCoeff M)

/-- Explicit divisor-free cap using the linear mollifier's square-root `ell^1` mass. -/
theorem levinsonCriticalDetectorLongEnergy_le_four_mul_M_mul_headEnergy
    (lam : ℝ) (L : ℕ) {M : ℕ} (hM : 1 < M) :
    levinsonCriticalDetectorLongEnergy lam L M ≤
      4 * M *
        ∑ n : Fin L,
          ‖Sieve.levinsonCriticalDetectorHeadCoeff lam ((n : ℕ) + 1)‖ ^ 2 := by
  let A : ℝ := ∑ n : Fin L,
    ‖Sieve.levinsonCriticalDetectorHeadCoeff lam ((n : ℕ) + 1)‖ ^ 2
  let B : ℝ := ∑ m : Fin M, ‖levinsonLinearMollifierFinCoeff M m‖
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  have hsqrtM : Real.sqrt (M : ℝ) ^ 2 = M := Real.sq_sqrt (by positivity)
  have hB_le : B ≤ 2 * Real.sqrt M :=
    sum_norm_levinsonLinearMollifierFinCoeff_le hM
  have hBsq := pow_le_pow_left₀ hB hB_le 2
  have hbase := levinsonCriticalDetectorLongEnergy_le_l2_l1 lam L M
  dsimp only [A, B] at *
  nlinarith

/-- Fully explicit divisor-free polynomial cap. -/
theorem levinsonCriticalDetectorLongEnergy_le_four_mul_M_mul_explicit
    (lam : ℝ) {L M : ℕ} (hL : 1 ≤ L) (hM : 1 < M) :
    levinsonCriticalDetectorLongEnergy lam L M ≤
      4 * M * ((1 + |lam| * Real.log L) ^ 2 * (1 + Real.log L)) := by
  refine (levinsonCriticalDetectorLongEnergy_le_four_mul_M_mul_headEnergy lam L hM).trans ?_
  exact mul_le_mul_of_nonneg_left
    (sum_normSq_levinsonCriticalDetectorHeadCoeff_le lam hL) (by positivity)

end RHTower
