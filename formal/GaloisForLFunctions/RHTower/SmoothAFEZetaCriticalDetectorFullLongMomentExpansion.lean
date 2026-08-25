import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorLongCoefficientDecomposition
import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifiedCriticalDetectorEnergy

/-!
# Arithmetic moment expansion of the full critical-detector long energy

The exact differentiated Barban--Vehov long tail is a quadratic polynomial in the detector
parameter.  Its three coefficients are now named finite harmonic moments; these are the scalar
arithmetic asymptotics required by the Levinson mean-square calculation.
-/

noncomputable section

namespace RHTower

open Finset

/-- Log-differentiated Barban--Vehov divisor coefficient before normalization. -/
def Sieve.barbanVehovDifferentiatedCoeff (M k : ℕ) : ℝ :=
  Sieve.barbanVehovLogMomentCoeff M k - Real.log k * Sieve.barbanVehovCoeff M k

/-- Base harmonic energy on the exact long product range. -/
def levinsonCriticalDetectorFullLongBaseMoment (L M : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc L (L * M),
    Sieve.barbanVehovCoeff M k ^ 2 / (k : ℝ)

/-- Mixed base/derivative harmonic moment on the exact long product range. -/
def levinsonCriticalDetectorFullLongCrossMoment (L M : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc L (L * M),
    Sieve.barbanVehovCoeff M k * Sieve.barbanVehovDifferentiatedCoeff M k / (k : ℝ)

/-- Differentiated harmonic energy on the exact long product range. -/
def levinsonCriticalDetectorFullLongDerivativeMoment (L M : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc L (L * M),
    Sieve.barbanVehovDifferentiatedCoeff M k ^ 2 / (k : ℝ)

/-- The full differentiated long energy is exactly a quadratic form in three arithmetic moments. -/
theorem levinsonCriticalDetectorFullLongEnergy_eq_momentQuadratic
    (lam : ℝ) (L : ℕ) {M : ℕ} (hM : 1 < M) :
    levinsonCriticalDetectorFullLongEnergy lam L M =
      (levinsonCriticalDetectorFullLongBaseMoment L M +
          2 * lam * levinsonCriticalDetectorFullLongCrossMoment L M +
          lam ^ 2 * levinsonCriticalDetectorFullLongDerivativeMoment L M) /
        Real.log M ^ 2 := by
  rw [levinsonCriticalDetectorFullLongEnergy_eq_sum_Ioc]
  rw [levinsonCriticalDetectorFullLongBaseMoment,
    levinsonCriticalDetectorFullLongCrossMoment,
    levinsonCriticalDetectorFullLongDerivativeMoment]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkpos : 0 < k := by
    have := (Finset.mem_Ioc.mp hk).1
    omega
  rw [Sieve.norm_levinsonLinearMollifiedCriticalDetectorCoeff_sq hM hkpos]
  rw [Sieve.barbanVehovDifferentiatedCoeff]
  ring

end RHTower
