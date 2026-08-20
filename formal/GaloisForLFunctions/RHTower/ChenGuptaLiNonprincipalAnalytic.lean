/-
# Chen--Gupta--Li non-principal detector regularity

The non-principal branch of the zero-detection contour has no Dirichlet
`L`-function pole.  This module makes that dichotomy explicit: its zero
certificates carry non-principality as checked data, and the corresponding
shifted detector factor is analytic everywhere.  Gamma remains meromorphic,
with its local cancellation at the certified zero supplied by
`ChenGuptaLiZeroResidue`.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiZeroResidue
import GaloisForLFunctions.RHTower.AnalyticDividedDifference
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles

open Complex LSeries DirichletCharacter Filter MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- A certified critical-strip zero of a non-principal Dirichlet character. -/
structure CGLNonprincipalCriticalStripLZero (q : ℕ) extends CGLCriticalStripLZero q where
  character_ne_one : character ≠ 1

/-- The translated finite detector factor in the non-principal branch. -/
def cglNonprincipalDetectorFactor (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) (w : ℂ) : ℂ :=
  zeroDetectionMobiusPolynomial X (q + 1) z.character (z.point + w) *
    DirichletCharacter.LFunction z.character (z.point + w)

/-- In the non-principal branch, the shifted finite detector factor is
complex differentiable everywhere. -/
theorem cglNonprincipalDetectorFactor_differentiable (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) :
    Differentiable ℂ (cglNonprincipalDetectorFactor X q z) := by
  intro w
  unfold cglNonprincipalDetectorFactor
  apply DifferentiableAt.mul
  · exact (differentiableAt_zeroDetectionMobiusPolynomial X (q + 1) z.character
      (z.point + w)).comp w
      ((differentiable_const z.point).differentiableAt.add differentiableAt_id)
  · exact (DirichletCharacter.differentiable_LFunction z.character_ne_one).differentiableAt.comp w
      ((differentiable_const z.point).differentiableAt.add differentiableAt_id)

/-- Hence the non-principal shifted detector factor is analytic at every
complex point. -/
theorem cglNonprincipalDetectorFactor_analyticAt (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) (w : ℂ) :
    AnalyticAt ℂ (cglNonprincipalDetectorFactor X q z) w :=
  (cglNonprincipalDetectorFactor_differentiable X q z).analyticAt w

/-- Apart from Gamma's known poles, the non-principal detector Mellin
integrand is meromorphic everywhere. -/
theorem cglNonprincipalDetectorMellinIntegrand_meromorphicAt (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) (w : ℂ) :
    MeromorphicAt (cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero) w := by
  unfold cglDetectorMellinIntegrand
  exact (Meromorphic.Gamma w).mul
    (cglNonprincipalDetectorFactor_analyticAt X q z w).meromorphicAt

/-- The translated non-principal detector factor vanishes at its certified
zero. -/
theorem cglNonprincipalDetectorFactor_zero (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) :
    cglNonprincipalDetectorFactor X q z 0 = 0 := by
  simpa [cglNonprincipalDetectorFactor] using
    cglDetectorMellinIntegrand_residueCoefficient_at_criticalZero X q z.toCGLCriticalStripLZero

/-- Removable divided difference of the zero-vanishing non-principal detector
factor. -/
def cglNonprincipalDetectorZeroQuotient (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) : ℂ → ℂ :=
  dslope (cglNonprincipalDetectorFactor X q z) 0

/-- The vanishing non-principal detector factor has the exact global linear
factor `w`, with a removable divided-difference quotient. -/
theorem cglNonprincipalDetectorFactor_eq_mul_zeroQuotient (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) (w : ℂ) :
    cglNonprincipalDetectorFactor X q z w =
      w * cglNonprincipalDetectorZeroQuotient X q z w := by
  simpa [cglNonprincipalDetectorZeroQuotient, smul_eq_mul] using
    (sub_smul_dslope_of_zero (cglNonprincipalDetectorFactor_zero X q z) w).symm

/-- The divided-difference quotient is analytic at every point. -/
theorem cglNonprincipalDetectorZeroQuotient_analyticAt (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) (w : ℂ) :
    AnalyticAt ℂ (cglNonprincipalDetectorZeroQuotient X q z) w := by
  unfold cglNonprincipalDetectorZeroQuotient
  exact analyticAt_dslope_of_analyticAt
    (cglNonprincipalDetectorFactor_analyticAt X q z 0)
    (cglNonprincipalDetectorFactor_analyticAt X q z w)

/-- The analytic replacement of the non-principal Mellin integrand after its
zero-cancelled Gamma pole is removed. -/
def cglNonprincipalRegularizedMellinIntegrand (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) (w : ℂ) : ℂ :=
  Complex.Gamma (w + 1) * cglNonprincipalDetectorZeroQuotient X q z w

/-- Away from `w = 0`, the original non-principal detector Mellin integrand
is exactly its regularized analytic replacement. -/
theorem cglNonprincipalMellinIntegrand_eq_regularized_off_zero (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) (w : ℂ) (hw : w ≠ 0) :
    cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero w =
      cglNonprincipalRegularizedMellinIntegrand X q z w := by
  rw [show cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero w =
    Complex.Gamma w * cglNonprincipalDetectorFactor X q z w by rfl,
    cglNonprincipalDetectorFactor_eq_mul_zeroQuotient,
    cglNonprincipalRegularizedMellinIntegrand]
  rw [Complex.Gamma_add_one w hw]
  ring

/-- The regularized non-principal Mellin integrand is analytic at the former
Gamma pole `w = 0`. -/
theorem cglNonprincipalRegularizedMellinIntegrand_analyticAt_zero (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) :
    AnalyticAt ℂ (cglNonprincipalRegularizedMellinIntegrand X q z) 0 := by
  unfold cglNonprincipalRegularizedMellinIntegrand
  apply AnalyticAt.mul
  · exact (HTGeometry.analyticAt_Gamma_of_re_pos (by norm_num)).comp
      (analyticAt_id.add analyticAt_const)
  · exact cglNonprincipalDetectorZeroQuotient_analyticAt X q z 0

end RHTower
