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

open Complex LSeries DirichletCharacter Filter MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- A certified critical-strip zero of a non-principal Dirichlet character. -/
structure CGLNonprincipalCriticalStripLZero (q : ℕ) extends CGLCriticalStripLZero q where
  character_ne_one : character ≠ 1

/-- In the non-principal branch, the shifted finite detector factor is
complex differentiable everywhere. -/
theorem cglNonprincipalDetectorFactor_differentiable (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) :
    Differentiable ℂ (fun w : ℂ =>
      zeroDetectionMobiusPolynomial X (q + 1) z.character (z.point + w) *
        DirichletCharacter.LFunction z.character (z.point + w)) := by
  intro w
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
    AnalyticAt ℂ (fun u : ℂ =>
      zeroDetectionMobiusPolynomial X (q + 1) z.character (z.point + u) *
        DirichletCharacter.LFunction z.character (z.point + u)) w :=
  (cglNonprincipalDetectorFactor_differentiable X q z).analyticAt w

/-- Apart from Gamma's known poles, the non-principal detector Mellin
integrand is meromorphic everywhere. -/
theorem cglNonprincipalDetectorMellinIntegrand_meromorphicAt (X q : ℕ)
    (z : CGLNonprincipalCriticalStripLZero q) (w : ℂ) :
    MeromorphicAt (cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero) w := by
  unfold cglDetectorMellinIntegrand
  exact (Meromorphic.Gamma w).mul
    (cglNonprincipalDetectorFactor_analyticAt X q z w).meromorphicAt

end RHTower
