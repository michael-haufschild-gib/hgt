import GaloisForLFunctions.RHTower.XiSafeHalfPlaneJacobiGammaRecovery
import GaloisForLFunctions.RHTower.CCM.CCMInverseTiltedDyadicPrimeTomography

/-!
# Safe-half-plane dyadic source window

The asymmetric Jacobi--Gamma recovery produces the coefficient

`v_x(k) = Lambda(k) * k⁻ˣ`

on every positive prime power.  Applying the literal inverse-tilted dyadic incidence gives the
fully specified safe window

`T_x(n) = sum_(n/2 < k <= n) v_x(k) * k/n`.

Replacing the von Mangoldt measure by its polar density forces the companion

`P_x(n) = ((1 - 2^(x-2)) / (2-x)) * n^(1-x)`.

Thus `2 * (P_x - T_x)` is a source-defined signed family with no free colligation parameter.  At
`x=1/2`, its prime column is exactly the existing inverse-tilted window and its polar coefficient
reduces on paper to `(4 - sqrt 2)/3`, the literal critical prime--polar row.

This file creates the exact safe source object and proves its coefficient and critical-window
identifications.  A boundary norm estimate is deliberately not postulated here: that estimate is
the remaining RH-bearing research problem.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace RHTower

/-- Literal dyadic window of the safe Jacobi-recovered von Mangoldt coefficients. -/
def xiSafeHalfPlaneDyadicWeightedPrimeWindow (x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Ioc (n / 2) n,
    (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-x)) * (k / n : ℝ)

/-- The safe window specializes exactly to the existing inverse-tilted critical window. -/
theorem xiSafeHalfPlaneDyadicWeightedPrimeWindow_half
    (n : ℕ) :
    xiSafeHalfPlaneDyadicWeightedPrimeWindow (1 / 2) n =
      inverseTiltedDyadicWeightedPrimeWindow n := by
  rw [xiSafeHalfPlaneDyadicWeightedPrimeWindow,
    inverseTiltedDyadicWeightedPrimeWindow]
  apply Finset.sum_congr rfl
  intro k hk
  have hkpos : 0 < k := by
    have hkleft := (Finset.mem_Ioc.mp hk).1
    omega
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  rw [show -(1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
    Real.rpow_neg hkreal.le, ← Real.sqrt_eq_rpow]
  ring

/-- Polar density forced by integrating `t^(1-x)` over the same multiplicative dyadic cell. -/
def xiSafeHalfPlaneDyadicPolarMain (x : ℝ) (n : ℕ) : ℝ :=
  ((1 - (2 : ℝ) ^ (x - 2)) / (2 - x)) * (n : ℝ) ^ (1 - x)

/-- The completely fixed safe prime--polar row, with signs joined before any norm. -/
def xiSafeHalfPlaneDyadicJoinedResidual (x : ℝ) (n : ℕ) : ℝ :=
  2 * (xiSafeHalfPlaneDyadicPolarMain x n -
    xiSafeHalfPlaneDyadicWeightedPrimeWindow x n)

theorem xiSafeHalfPlaneDyadicJoinedResidual_eq
    (x : ℝ) (n : ℕ) :
    xiSafeHalfPlaneDyadicJoinedResidual x n =
      2 * xiSafeHalfPlaneDyadicPolarMain x n -
        2 * xiSafeHalfPlaneDyadicWeightedPrimeWindow x n := by
  rw [xiSafeHalfPlaneDyadicJoinedResidual]
  ring

/-- At the critical boundary, the joined row uses the literal inverse-tilted prime window. -/
theorem xiSafeHalfPlaneDyadicJoinedResidual_half_eq
    (n : ℕ) :
    xiSafeHalfPlaneDyadicJoinedResidual (1 / 2) n =
      2 * xiSafeHalfPlaneDyadicPolarMain (1 / 2) n -
        2 * inverseTiltedDyadicWeightedPrimeWindow n := by
  rw [xiSafeHalfPlaneDyadicJoinedResidual_eq,
    xiSafeHalfPlaneDyadicWeightedPrimeWindow_half]

/-- On an actual prime-power index, the safe arithmetic window coefficient is exactly the
coefficient produced by Jacobi--Gamma recovery. -/
theorem vonMangoldt_primePower_mul_rpow_eq_xiSafeHalfPlaneCoefficient
    (x : ℝ) (p : Nat.Primes) (e : ℕ) :
    ArithmeticFunction.vonMangoldt (p ^ (e + 1)) *
        ((p ^ (e + 1) : ℕ) : ℝ) ^ (-x) =
      xiSafeHalfPlanePrimePowerCoefficient x p e := by
  let P : ℝ := p
  have hP : 0 < P := by
    dsimp only [P]
    exact_mod_cast p.2.pos
  have hpowNat : 0 < p.1 ^ (e + 1) := pow_pos p.2.pos _
  have hpow : (0 : ℝ) < ((p ^ (e + 1) : ℕ) : ℝ) := by
    exact_mod_cast hpowNat
  rw [vonMangoldt_prime_pow_succ_eq_log (p, e),
    xiSafeHalfPlanePrimePowerCoefficient]
  congr 1
  rw [xiMobiusContinuousApertureDiskNode_pow,
    Real.rpow_def_of_pos hpow]
  congr 1
  rw [Nat.cast_pow, Real.log_pow]
  push_cast
  ring

/-- Consequently every prime-power summand of the safe window is literally the recovered source
coefficient times the physical dyadic incidence weight. -/
theorem safeDyadicPrimePowerSummand_eq_recoveredCoefficient
    (x : ℝ) (n : ℕ) (p : Nat.Primes) (e : ℕ) :
    (ArithmeticFunction.vonMangoldt (p ^ (e + 1)) *
        (((p ^ (e + 1) : ℕ) : ℝ) ^ (-x))) *
          ((p ^ (e + 1) : ℕ) / n : ℝ) =
      xiSafeHalfPlanePrimePowerCoefficient x p e *
        ((p ^ (e + 1) : ℕ) / n : ℝ) := by
  rw [vonMangoldt_primePower_mul_rpow_eq_xiSafeHalfPlaneCoefficient]

end RHTower
