import GaloisForLFunctions.RHTower.BurnolCoPoissonConormalReflectionCover
import GaloisForLFunctions.RHTower.DeningerCofinalCountercharacterTopBoundaryTransgression
import GaloisForLFunctions.RHTower.XiCriticalLineIntegrality

/-!
# Deninger--Burnol conormal radial top-boundary comparison

Actual multiplicity-exact Burnol sub-window Mellin jets recover a centered
complex source character.  At ordinary-integer logarithmic aperture, its
reflected squared-norm defect is exactly the Deninger tensor-square mate
curvature, hence exactly the coefficient of the concrete cofinal Tate top
boundary.  At clock six this also identifies the actual Gamma boundary and
completed Calderon--Witt incidence value.

The conormal jet itself is nonzero at every Xi divisor.  Thus this comparison
is coefficient-faithful and cannot be used as a generic Stokes annihilation;
its radial defect vanishes exactly on the critical line.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Half-density centered character obtained from the ratio of the actual
multiplicity-exact Burnol windows of logarithmic lengths `log n` and
`2 * log n`. -/
def deningerBurnolActualCenteredConormalCharacter
    (n : ℕ) (rho : XiDivisorSupport) : ℂ :=
  Complex.exp (-((Real.log (n : ℝ) : ℝ) : ℂ) / 2) *
    burnolCoPoissonActualDoubledWindowConormalRatio
      (Real.log (n : ℝ)) rho

/-- The actual nested-window character is the literal centered Burnol
conormal character. -/
theorem deningerBurnolActualCenteredConormalCharacter_eq
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport) :
    deningerBurnolActualCenteredConormalCharacter n rho =
      burnolCoPoissonCenteredConormalCharacter
        (Real.log (n : ℝ)) (rho : ℂ) := by
  have hnR : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_lt_two hn
  rw [deningerBurnolActualCenteredConormalCharacter,
    burnolCoPoissonActualDoubledWindowConormalRatio_eq_exp
      (Real.log_pos hnR)]
  rw [burnolCoPoissonCenteredConormalCharacter, ← Complex.exp_add]
  congr 1
  ring

/-- The exact-multiplicity Burnol conormal jet is nonzero at every Xi
divisor and every nontrivial ordinary-integer aperture. -/
theorem iteratedDeriv_burnolCoPoissonExpWindowZetaMellinGerm_log_nat_ne_zero
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport) :
    iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (burnolCoPoissonExpWindowZetaMellinGerm (Real.log (n : ℝ)))
        (rho : ℂ) ≠ 0 := by
  have hnR : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_lt_two hn
  rw [iteratedDeriv_burnolCoPoissonExpWindowZetaMellinGerm]
  exact burnolCoPoissonSubWindowConormalCoefficient_ne_zero
    (Real.log_pos hnR) (xi_divisor_support_re_mem_open_unit rho).1
    (burnolCoPoissonXiConormalLead_ne_zero rho)

/-- Squared norm of the actual centered Burnol conormal character is exactly
the Deninger half-density mate gain. -/
theorem norm_deningerBurnolActualCenteredConormalCharacter_sq
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport) :
    ‖deningerBurnolActualCenteredConormalCharacter n rho‖ ^ (2 : ℕ) =
      deningerHalfDensityMateGain n (rho : ℂ) := by
  rw [deningerBurnolActualCenteredConormalCharacter_eq hn,
    norm_burnolCoPoissonCenteredConormalCharacter,
    deningerHalfDensityMateGain, ← Real.exp_nat_mul]
  congr 1
  ring

/-- Reflected radial discriminant of the actual multiplicity-exact Burnol
conormal pair. -/
def deningerBurnolActualConormalRadialReflectionDefect
    (n : ℕ) (rho : XiDivisorSupport) : ℝ :=
  ‖deningerBurnolActualCenteredConormalCharacter n rho‖ ^ (2 : ℕ) -
    ‖deningerBurnolActualCenteredConormalCharacter n
      (xiZeroLineConjEquiv rho)‖ ^ (2 : ℕ)

/-- The physical Burnol conormal radial discriminant is exactly Deninger's
tensor-square mate curvature. -/
theorem deningerBurnolActualConormalRadialReflectionDefect_eq
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport) :
    deningerBurnolActualConormalRadialReflectionDefect n rho =
      deningerTensorSquareRadialMateCurvature n (rho : ℂ) := by
  rw [deningerBurnolActualConormalRadialReflectionDefect,
    norm_deningerBurnolActualCenteredConormalCharacter_sq hn,
    norm_deningerBurnolActualCenteredConormalCharacter_sq hn,
    xiZeroLineConjEquiv_apply]
  change deningerHalfDensityMateGain n (rho : ℂ) -
      deningerHalfDensityMateGain n (1 - star (rho : ℂ)) = _
  rw [deningerHalfDensityMateGain_reflection,
    deningerHalfDensityMateGain_sub_inv_eq_mateCurvature
      (lt_of_lt_of_le Nat.zero_lt_two hn)]

/-- The concrete relative cofinal top-boundary reader is the actual Burnol
conormal radial reflection defect. -/
theorem deningerCofinalTopBoundaryCoefficient_eq_burnolConormalRadialDefect
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport) (m : ℕ) :
    deningerCofinalTopBoundaryCoefficient m
        (deningerRelativeCofinalTateDefect
            (1 - star (rho : ℂ)) n m
              (tateClockFinIntervalBasis ℝ (Fin.last m)) -
          deningerRelativeCofinalTateDefect
            (rho : ℂ) n m
              (tateClockFinIntervalBasis ℝ (Fin.last m))) =
      deningerBurnolActualConormalRadialReflectionDefect n rho := by
  rw [deningerCofinalTopBoundaryCoefficient_reflectedRelativeDefect
      (lt_of_lt_of_le Nat.zero_lt_two hn),
    deningerBurnolActualConormalRadialReflectionDefect_eq hn]

/-- At clock six the actual Gamma/Calderon--Witt coefficient is the positive
calibration of the physical Burnol conormal radial defect. -/
theorem deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_burnolConormal
    (r : XiZeroCopy) :
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient r =
      (((deningerCalderonWittBaseGammaMateCalibration *
        deningerBurnolActualConormalRadialReflectionDefect 6 r.1 : ℝ) : ℂ)) := by
  rw [deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_tensorSquareMateCurvature,
    deningerBurnolActualConormalRadialReflectionDefect_eq (by norm_num : 2 ≤ 6)]

/-- Decoding the completed incidence landing gives the physical Burnol
radial defect times the same nonzero cross-prime incidence witness. -/
theorem deningerCofinalRelativeBocksteinIncidence_sourceValue_eq_burnolConormal
    (p q : Nat.Primes) (hpq : p ≠ q)
    (r : XiZeroCopy) (m : ℕ) :
    deningerCalderonWittCrossPrimeXiIncidenceCompletionSourceValue
        p q hpq r
        (deningerCofinalRelativeBocksteinIncidence p q hpq r m) =
      ((deningerBurnolActualConormalRadialReflectionDefect 6 r.1 : ℝ) : ℂ) •
        deningerCalderonWittCrossPrimeGammaWitness hpq := by
  rw [deningerCofinalRelativeBocksteinIncidence_sourceValue,
    deningerBurnolActualConormalRadialReflectionDefect_eq
      (by norm_num : 2 ≤ 6)]

/-- The physical radial defect has exactly the critical-line zero set.  This
is a classification, not an assertion that it vanishes on every Xi divisor. -/
theorem deningerBurnolActualConormalRadialReflectionDefect_eq_zero_iff
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport) :
    deningerBurnolActualConormalRadialReflectionDefect n rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [deningerBurnolActualConormalRadialReflectionDefect_eq hn,
    deningerTensorSquareRadialMateCurvature_eq_zero_iff n (rho : ℂ) hn]

end

end RHTower
