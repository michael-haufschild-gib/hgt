import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSeedZeroMean
import GaloisForLFunctions.HTGeometry.ReflectionIntegral

/-!
# Critical Euler atom has zero full-line Mellin charge

The exact theta Gaussian seed has zero radial integral. Exponential substitution and
logarithmic translation transfer this to every literal source atom: its integral against
`exp (x / 2)` is zero. The completed all-integer source has integral `1/2`, as proved in
`PrimeArchThetaWardLaplaceHalfDensity`; that finite-to-infinite boundary anomaly is
analyzed in the paper card `theta-euler-critical-boundary-mass-escape.md`.
-/

open MeasureTheory

namespace RHTower

/-- The logarithmic Gaussian seed has zero critical Mellin charge. -/
theorem integral_exp_half_mul_thetaCuspLogSeed_zero :
    (∫ x : ℝ, Real.exp (x / 2) * thetaCuspLogSeed x) = 0 := by
  rw [← integral_thetaCuspSeed_Ioi_eq_zero,
    GaloisForLFunctions.HTGeometry.integral_Ioi_comp_exp]
  apply integral_congr_ae
  filter_upwards [] with x
  dsimp [thetaCuspLogSeed]
  rw [← mul_assoc, ← Real.exp_add]
  congr 1
  ring

/-- Every literal integer theta atom has zero critical Mellin charge. -/
theorem integral_exp_half_mul_thetaCuspSourceTerm_zero
    (n : ℕ) (hn : 0 < n) :
    (∫ x : ℝ, Real.exp (x / 2) * thetaCuspSourceTerm x n) = 0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfun (x : ℝ) :
      Real.exp (x / 2) * thetaCuspSourceTerm x n =
        (n : ℝ)⁻¹ *
          (Real.exp ((x + Real.log n) / 2) *
            thetaCuspLogSeed (x + Real.log n)) := by
    have hleft :
        Real.exp (x / 2) * thetaCuspSourceTerm x n =
          Real.exp x * thetaCuspSeed (n * Real.exp x) := by
      simp only [thetaCuspSourceTerm]
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      ring
    have hright :
        Real.exp ((x + Real.log n) / 2) *
            thetaCuspLogSeed (x + Real.log n) =
          Real.exp (x + Real.log n) *
            thetaCuspSeed (Real.exp (x + Real.log n)) := by
      simp only [thetaCuspLogSeed]
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      ring
    rw [hleft, hright, Real.exp_add, Real.exp_log hnR]
    field_simp
  have hshift :
      (∫ x : ℝ, Real.exp (x / 2) * thetaCuspSourceTerm x n) =
        (n : ℝ)⁻¹ *
          ∫ y : ℝ, Real.exp (y / 2) * thetaCuspLogSeed y := by
    calc
      _ = ∫ x : ℝ, (n : ℝ)⁻¹ *
          (Real.exp ((x + Real.log n) / 2) *
            thetaCuspLogSeed (x + Real.log n)) := by
              apply integral_congr_ae
              filter_upwards [] with x
              exact hfun x
      _ = (n : ℝ)⁻¹ * ∫ x : ℝ,
          Real.exp ((x + Real.log n) / 2) *
            thetaCuspLogSeed (x + Real.log n) := by rw [integral_const_mul]
      _ = _ := by
        congr 1
        exact integral_add_right_eq_self
          (fun y : ℝ => Real.exp (y / 2) * thetaCuspLogSeed y) (Real.log n)
  rw [hshift, integral_exp_half_mul_thetaCuspLogSeed_zero, mul_zero]

end RHTower
