import GaloisForLFunctions.RHTower.DeningerCenteredFlowCountercharacterRelativeCurvatureNoGo
import GaloisForLFunctions.RHTower.DeningerCalderonWittCompletedXiGreenIncidenceComparison
import GaloisForLFunctions.RHTower.TateKummerWoldGammaIntervalCharacter

/-!
# Cofinal countercharacter top-boundary transgression

The relative raw-to-countertransported Deninger curvature has a literal
finite-stage source representative.  Scale the finite Tate forward arrows
by one fixed power-clock gain.  Their cofinal naturality defect is that gain
times the rank-one Tate top boundary.  Subtracting the raw gain from the
covariantly flat gain therefore realizes the relative curvature on the
actual cofinal Bockstein generator.

Critical reflection polarizes this relative defect to the Deninger
tensor-square mate curvature times the nonzero top boundary.  Reading the
new top coordinate recovers the mate curvature exactly; at clock six this
is the actual Gamma/Calderon--Witt coefficient up to its existing positive
calibration.  A finite-support Xi vector then lands the retained coefficient
in the already constructed completed cross-prime incidence carrier.

No source Stokes annihilation is asserted.  On the contrary, the exact zero
set proves that such annihilation is the remaining RH-bearing arithmetic
theorem and cannot follow from finite interval exactness alone.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Scaled Tate naturality defects -/

/-- Finite Tate forward arrow with one fixed radial gain. -/
def deningerScaledTateForward (gain : ℝ) (m : ℕ) :
    (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) :=
  gain • tateClockFinIntervalForward ℝ m

/-- Failure of the scaled finite forward arrows to commute with cofinal
zero-extension. -/
def deningerScaledTateForwardNaturalityDefect
    (gain : ℝ) (m : ℕ) (f : Fin (m + 1) → ℝ) :
    Fin (m + 2) → ℝ :=
  deningerScaledTateForward gain (m + 1)
      (tateClockFinIntervalInclusion ℝ (m + 1) f) -
    tateClockFinIntervalInclusion ℝ (m + 1)
      (deningerScaledTateForward gain m f)

/-- The scaled naturality defect is exactly the gain times the canonical
rank-one cofinal top boundary. -/
theorem deningerScaledTateForwardNaturalityDefect_eq_topBoundary
    (gain : ℝ) (m : ℕ) (f : Fin (m + 1) → ℝ) :
    deningerScaledTateForwardNaturalityDefect gain m f =
      gain • tateClockFinIntervalTopBoundary ℝ m f := by
  simp only [deningerScaledTateForwardNaturalityDefect,
    deningerScaledTateForward, LinearMap.smul_apply, map_smul]
  rw [tateClockFinIntervalForward_inclusion_defect]
  module

/-! ## Relative raw-to-flat preclosure class -/

/-- Raw Deninger cofinal defect at a fixed power clock. -/
def deningerRawCofinalTateDefect
    (s : ℂ) (n m : ℕ) (f : Fin (m + 1) → ℝ) :
    Fin (m + 2) → ℝ :=
  deningerScaledTateForwardNaturalityDefect
    (deningerHalfDensityMateGain n s) m f

/-- Covariantly flat cofinal defect after centered-flow countertransport. -/
def deningerCountertransportedCofinalTateDefect
    (m : ℕ) (f : Fin (m + 1) → ℝ) :
    Fin (m + 2) → ℝ :=
  deningerScaledTateForwardNaturalityDefect 1 m f

/-- Flat-minus-raw relative cofinal defect.  This retains the gauge anomaly
which absolute countertransport erases. -/
def deningerRelativeCofinalTateDefect
    (s : ℂ) (n m : ℕ) (f : Fin (m + 1) → ℝ) :
    Fin (m + 2) → ℝ :=
  deningerCountertransportedCofinalTateDefect m f -
    deningerRawCofinalTateDefect s n m f

/-- The scalar relative Deninger curvature is the coefficient of the
literal Tate top-boundary class. -/
theorem deningerRelativeCofinalTateDefect_eq
    (s : ℂ) (n m : ℕ) (f : Fin (m + 1) → ℝ) :
    deningerRelativeCofinalTateDefect s n m f =
      deningerCenteredFlowRelativeReducedCurvature s n •
        tateClockFinIntervalTopBoundary ℝ m f := by
  rw [deningerRelativeCofinalTateDefect,
    deningerCountertransportedCofinalTateDefect,
    deningerRawCofinalTateDefect,
    deningerScaledTateForwardNaturalityDefect_eq_topBoundary,
    deningerScaledTateForwardNaturalityDefect_eq_topBoundary,
    deningerCenteredFlowRelativeReducedCurvature_eq]
  module

/-- Critical reflection polarizes the concrete relative cofinal defect to
the Deninger tensor-square mate curvature times the retained top boundary. -/
theorem deningerRelativeCofinalTateDefect_reflection_sub_source
    {n : ℕ} (hn : 0 < n) (s : ℂ) (m : ℕ)
    (f : Fin (m + 1) → ℝ) :
    deningerRelativeCofinalTateDefect (1 - star s) n m f -
        deningerRelativeCofinalTateDefect s n m f =
      deningerTensorSquareRadialMateCurvature n s •
        tateClockFinIntervalTopBoundary ℝ m f := by
  rw [deningerRelativeCofinalTateDefect_eq,
    deningerRelativeCofinalTateDefect_eq, ← sub_smul,
    deningerCenteredFlowRelativeReducedCurvature_reflection_sub_source
      hn s]

/-! ## Exact top-coordinate reader -/

/-- Reader of the newly created top coordinate at cofinal stage `m`. -/
def deningerCofinalTopBoundaryCoefficient
    (m : ℕ) (v : Fin (m + 2) → ℝ) : ℝ :=
  v (Fin.last (m + 1))

/-- The reader normalizes the canonical top-boundary generator to one. -/
@[simp]
theorem deningerCofinalTopBoundaryCoefficient_topBoundary_basis_last
    (m : ℕ) :
    deningerCofinalTopBoundaryCoefficient m
        (tateClockFinIntervalTopBoundary ℝ m
          (tateClockFinIntervalBasis ℝ (Fin.last m))) = 1 := by
  rw [tateClockFinIntervalTopBoundary_basis_last]
  simp [deningerCofinalTopBoundaryCoefficient,
    tateClockFinIntervalBasis]

/-- The top-coordinate reader recovers the complete reflected Deninger mate
curvature, with no scalar or completion loss. -/
theorem deningerCofinalTopBoundaryCoefficient_reflectedRelativeDefect
    {n : ℕ} (hn : 0 < n) (s : ℂ) (m : ℕ) :
    deningerCofinalTopBoundaryCoefficient m
        (deningerRelativeCofinalTateDefect (1 - star s) n m
            (tateClockFinIntervalBasis ℝ (Fin.last m)) -
          deningerRelativeCofinalTateDefect s n m
            (tateClockFinIntervalBasis ℝ (Fin.last m))) =
      deningerTensorSquareRadialMateCurvature n s := by
  rw [deningerRelativeCofinalTateDefect_reflection_sub_source
    hn s m, tateClockFinIntervalTopBoundary_basis_last]
  simp [deningerCofinalTopBoundaryCoefficient,
    tateClockFinIntervalBasis]

/-- The retained reflected preclosure class vanishes exactly on the
critical half-density section.  Thus finite exactness cannot annihilate it
off the critical line. -/
theorem deningerRelativeCofinalTateDefect_reflected_basis_eq_zero_iff
    {n : ℕ} (hn : 2 ≤ n) (s : ℂ) (m : ℕ) :
    deningerRelativeCofinalTateDefect (1 - star s) n m
          (tateClockFinIntervalBasis ℝ (Fin.last m)) -
        deningerRelativeCofinalTateDefect s n m
          (tateClockFinIntervalBasis ℝ (Fin.last m)) = 0 ↔
      s.re = 1 / 2 := by
  constructor
  · intro hzero
    have hcurvature :
        deningerTensorSquareRadialMateCurvature n s = 0 := by
      calc
        deningerTensorSquareRadialMateCurvature n s =
            deningerCofinalTopBoundaryCoefficient m
              (deningerRelativeCofinalTateDefect (1 - star s) n m
                  (tateClockFinIntervalBasis ℝ (Fin.last m)) -
                deningerRelativeCofinalTateDefect s n m
                  (tateClockFinIntervalBasis ℝ (Fin.last m))) :=
          (deningerCofinalTopBoundaryCoefficient_reflectedRelativeDefect
            (lt_of_lt_of_le Nat.zero_lt_two hn) s m).symm
        _ = deningerCofinalTopBoundaryCoefficient m 0 := by
          exact congrArg (deningerCofinalTopBoundaryCoefficient m) hzero
        _ = 0 := rfl
    exact
      (deningerTensorSquareRadialMateCurvature_eq_zero_iff
        n s hn).1 hcurvature
  · intro hline
    rw [deningerRelativeCofinalTateDefect_reflection_sub_source
      (lt_of_lt_of_le Nat.zero_lt_two hn) s m,
      (deningerTensorSquareRadialMateCurvature_eq_zero_iff
        n s hn).2 hline,
      zero_smul]

/-! ## Actual Gamma and completed-incidence landing -/

/-- At the forced `(2,3)` clock, the actual Gamma/Calderon--Witt boundary
coefficient is the positive calibration of the concrete cofinal
top-boundary coordinate. -/
theorem
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_cofinalTopBoundary
    (r : XiZeroCopy) (m : ℕ) :
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient r =
      ((deningerCalderonWittBaseGammaMateCalibration *
        deningerCofinalTopBoundaryCoefficient m
          (deningerRelativeCofinalTateDefect
              (1 - star (r.1 : ℂ)) 6 m
                (tateClockFinIntervalBasis ℝ (Fin.last m)) -
            deningerRelativeCofinalTateDefect
              (r.1 : ℂ) 6 m
                (tateClockFinIntervalBasis ℝ (Fin.last m))) : ℝ) : ℂ) := by
  rw [deningerCofinalTopBoundaryCoefficient_reflectedRelativeDefect
      (n := 6) (by norm_num) (r.1 : ℂ) m,
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_tensorSquareMateCurvature]

/-- One finite-support completed Xi vector carrying the coefficient read
from the concrete relative cofinal top boundary. -/
def deningerCofinalRelativeBocksteinXiVector
    (r : XiZeroCopy) (m : ℕ) : DeningerArithmeticCompletedH1 :=
  lp.single 2 r
    ((deningerCofinalTopBoundaryCoefficient m
      (deningerRelativeCofinalTateDefect
          (1 - star (r.1 : ℂ)) 6 m
            (tateClockFinIntervalBasis ℝ (Fin.last m)) -
        deningerRelativeCofinalTateDefect
          (r.1 : ℂ) 6 m
            (tateClockFinIntervalBasis ℝ (Fin.last m))) : ℝ) : ℂ)

/-- Coefficient-faithful landing of the cofinal relative Bockstein vector
in the completed cross-prime Calderon--Witt incidence carrier. -/
def deningerCofinalRelativeBocksteinIncidence
    (p q : Nat.Primes) (hpq : p ≠ q)
    (r : XiZeroCopy) (m : ℕ) :
    DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq :=
  deningerCompletedXiToCrossPrimeIncidenceCompletion p q hpq
    (deningerCofinalRelativeBocksteinXiVector r m)

/-- Decoding the completed incidence landing at its divisor coordinate
recovers mate curvature times the actual nonzero cross-prime incidence
witness. -/
theorem deningerCofinalRelativeBocksteinIncidence_sourceValue
    (p q : Nat.Primes) (hpq : p ≠ q)
    (r : XiZeroCopy) (m : ℕ) :
    deningerCalderonWittCrossPrimeXiIncidenceCompletionSourceValue
        p q hpq r
        (deningerCofinalRelativeBocksteinIncidence p q hpq r m) =
      ((deningerTensorSquareRadialMateCurvature 6 (r.1 : ℂ) : ℝ) : ℂ) •
        deningerCalderonWittCrossPrimeGammaWitness hpq := by
  rw [deningerCofinalRelativeBocksteinIncidence,
    deningerCalderonWittCrossPrimeXiIncidenceCompletionSourceValue_xi,
    deningerCofinalRelativeBocksteinXiVector,
    deningerCofinalTopBoundaryCoefficient_reflectedRelativeDefect
      (n := 6) (by norm_num) (r.1 : ℂ) m]
  simp

/-- The completed source incidence value loses no information: it vanishes
exactly when the actual Gamma boundary coefficient vanishes. -/
theorem deningerCofinalRelativeBocksteinIncidence_sourceValue_eq_zero_iff_gamma
    (p q : Nat.Primes) (hpq : p ≠ q)
    (r : XiZeroCopy) (m : ℕ) :
    deningerCalderonWittCrossPrimeXiIncidenceCompletionSourceValue
        p q hpq r
        (deningerCofinalRelativeBocksteinIncidence p q hpq r m) = 0 ↔
      deningerCalderonWittBaseGammaBoundaryDefectCoefficient r = 0 := by
  rw [deningerCofinalRelativeBocksteinIncidence_sourceValue]
  simp only [smul_eq_zero,
    deningerCalderonWittCrossPrimeGammaWitness_ne_zero p q hpq,
    or_false, Complex.ofReal_eq_zero]
  rw [deningerTensorSquareRadialMateCurvature_eq_zero_iff
      6 (r.1 : ℂ) (by norm_num),
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_zero_iff]

end

end RHTower
