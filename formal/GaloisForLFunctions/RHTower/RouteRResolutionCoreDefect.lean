import GaloisForLFunctions.HTGeometry.ResolutionExactnessProfile
import GaloisForLFunctions.RHTower.RouteRCompletionMigrationDefect

/-!
# Route R resolution-core completion defect

Gamma damping gives the fixed-tail completion defect a sharp aperture wall.  At horizontal grade
`t`, the damped Roos class is exact precisely above aperture `|t|`, except that neutral grade is
identically exact.  This file packages that theorem as an actual resolution-exactness profile.

For an Xi support point `rho`, the core radius is therefore
`|2 * Re rho - 1|`.  A physical defect is cofinally resolvable when its canonical damped source
class remains exact along positive apertures closing to zero.  This happens exactly on the critical
line.  Global cofinal resolvability is equivalent to RH.

No zero is generated.  An off-line zero is classified as a completion defect with a strictly
positive, coefficient-faithful resolution core.
-/

open Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.BoundaryMigration

namespace RHTower

noncomputable section

/-- Canonical Gamma-damped tail class at aperture `epsilon` and horizontal grade `t`. -/
def routeRPrimeGammaApertureTailClass (epsilon t : ℝ) :=
  routeRDiagonalTailRoosClass
    (routeRPrimeGammaDampedBocksteinSequence epsilon t)

/-- Sharp resolution profile of the coefficient-faithful prime--Gamma completion defect. -/
def routeRPrimeGammaResolutionExactnessProfile
    (t : ℝ) : ResolutionExactnessProfile where
  coreRadius := |t|
  coreRadius_nonneg := abs_nonneg t
  exactAt epsilon := routeRPrimeGammaApertureTailClass epsilon t = 0
  exactAt_iff epsilon := by
    rw [routeRPrimeGammaApertureTailClass,
      routeRDiagonalTailRoosClass_eq_zero_iff_summable,
      summable_routeRPrimeGammaDampedBocksteinSequence_iff]
    simp only [abs_eq_zero]

/-- Aperture exactness is absence of the canonically damped defect from the fixed target flag. -/
theorem routeRPrimeGammaResolutionExactAt_iff_no_survival
    (epsilon t : ℝ) :
    (routeRPrimeGammaResolutionExactnessProfile t).exactAt epsilon ↔
      routeRTailRoosExactnessFlag ∉ ExFlag.survival
        (routeRDiagonalMismatchInIdeal
          (routeRPrimeGammaDampedBocksteinSequence epsilon t)) := by
  have h := derivedLimitClass_ne_zero_iff_survival
    (k := ℂ) (fun _ : ℕ => routeRSummableSequenceIdeal)
    routeRTailRoosRestrictedBond
    (routeRDiagonalMismatchInIdeal
      (routeRPrimeGammaDampedBocksteinSequence epsilon t))
  change routeRDiagonalTailRoosClass
      (routeRPrimeGammaDampedBocksteinSequence epsilon t) = 0 ↔ _
  simpa [routeRDiagonalTailRoosClass, routeRTailRoosExactnessFlag,
    routeRTailRoosBoundary, derivedLimitExactnessFlag] using not_congr h

/-- A fixed grade has exact source primitives through a cofinal closing aperture exactly at
neutral grade. -/
theorem routeRPrimeGammaCofinallyExact_iff_grade_eq_zero (t : ℝ) :
    (routeRPrimeGammaResolutionExactnessProfile t).CofinallyExact ↔ t = 0 := by
  rw [ResolutionExactnessProfile.cofinallyExact_iff_coreRadius_eq_zero]
  simp [routeRPrimeGammaResolutionExactnessProfile]

/-- Resolution core of the physical completion defect carried by one Xi support point. -/
def routeRPrimeGammaXiResolutionCoreRadius (rho : XiDivisorSupport) : ℝ :=
  |2 * (rho : ℂ).re - 1|

/-- The physical resolution core vanishes exactly on the critical line. -/
theorem routeRPrimeGammaXiResolutionCoreRadius_eq_zero_iff
    (rho : XiDivisorSupport) :
    routeRPrimeGammaXiResolutionCoreRadius rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [routeRPrimeGammaXiResolutionCoreRadius, abs_eq_zero]
  constructor <;> intro h <;> linarith

/-- An actual Xi completion defect is cofinally resolvable exactly on the critical line. -/
theorem routeRPrimeGammaXiCofinallyExact_iff_re_eq_half
    (rho : XiDivisorSupport) :
    (routeRPrimeGammaResolutionExactnessProfile
      (2 * (rho : ℂ).re - 1)).CofinallyExact ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [routeRPrimeGammaCofinallyExact_iff_grade_eq_zero]
  constructor <;> intro h <;> linarith

/-- Every physical completion defect admits exact primitives through arbitrarily fine canonical
Gamma apertures. -/
def RouteRPrimeGammaXiGloballyCofinallyExact : Prop :=
  ∀ rho : XiDivisorSupport,
    (routeRPrimeGammaResolutionExactnessProfile
      (2 * (rho : ℂ).re - 1)).CofinallyExact

/-- Global cofinal resolution exactness is RH. -/
theorem routeRPrimeGammaXiGloballyCofinallyExact_iff_riemannHypothesis :
    RouteRPrimeGammaXiGloballyCofinallyExact ↔ RiemannHypothesis := by
  rw [← routeRPrimeGammaXiGlobalCompletionEscapeFree_iff_riemannHypothesis]
  constructor
  · intro h rho
    exact (routeRPrimeGammaXiCompletionEscapeClass_eq_zero_iff_re_eq_half rho).2
      ((routeRPrimeGammaXiCofinallyExact_iff_re_eq_half rho).1 (h rho))
  · intro h rho
    exact (routeRPrimeGammaXiCofinallyExact_iff_re_eq_half rho).2
      ((routeRPrimeGammaXiCompletionEscapeClass_eq_zero_iff_re_eq_half rho).1 (h rho))

/-- Equivalent defect form: RH says every physical resolution core is zero. -/
theorem riemannHypothesis_iff_all_routeRPrimeGammaXiResolutionCoreRadius_eq_zero :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        routeRPrimeGammaXiResolutionCoreRadius rho = 0 := by
  rw [← routeRPrimeGammaXiGloballyCofinallyExact_iff_riemannHypothesis]
  constructor
  · intro h rho
    exact (routeRPrimeGammaXiResolutionCoreRadius_eq_zero_iff rho).2
      ((routeRPrimeGammaXiCofinallyExact_iff_re_eq_half rho).1 (h rho))
  · intro h rho
    exact (routeRPrimeGammaXiCofinallyExact_iff_re_eq_half rho).2
      ((routeRPrimeGammaXiResolutionCoreRadius_eq_zero_iff rho).1 (h rho))

end

end RHTower
