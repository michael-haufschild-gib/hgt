import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62CriticalMultipliers
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FiniteContour

/-!
# Chen--Gupta--Li Lemma 6.2: finite critical-line integrand

At the reflected finite contour's critical line, the functional-equation and
imprimitive Euler multipliers are unimodular.  Thus the integrand has exactly
the Mellin-transform, `N^(1/2)`, and dual Dirichlet-prefix norm that occurs in
CGL's `I₁` term.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- Exact norm identity for CGL's finite reflected integrand on `Re(s)=1/2`.
The source's finite dual Dirichlet polynomial remains as a literal prefix. -/
theorem cglLemma62_finiteCritical_norm_eq
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : ℕ) (u : ℝ) :
    ‖cglLemma62FiniteContourIntegrand w N B t M (cglLemma62CriticalPoint u).value‖ =
      ‖cglLemma62MellinTransform w (cglLemma62CriticalPoint u).value‖ *
        (N.value : ℝ) ^ (1 / 2 : ℝ) *
          ‖cglLemma62DirichletHead B.character⁻¹ M
            (1 - (cglLemma62CriticalPoint u).value + (t : ℂ) * I)‖ := by
  have hshift : (cglLemma62CriticalPoint u).value - (t : ℂ) * I =
      (cglLemma62CriticalPoint (u - t)).value := by
    unfold cglLemma62CriticalPoint
    push_cast
    ring
  have hfunctional : ‖cglLemma62PrimitiveFunctionalFactor B.primitive
      ((cglLemma62CriticalPoint u).value - (t : ℂ) * I)‖ = 1 := by
    rw [hshift]
    exact cglLemma62_primitiveFunctionalFactor_critical_norm_one B.primitive
      (cglLemma62CriticalPoint (u - t))
  have hEuler : ‖cglLemma62EulerCorrectionAt B
      ((cglLemma62CriticalPoint u).value - (t : ℂ) * I)‖ = 1 := by
    rw [hshift]
    exact cglLemma62EulerCorrectionAt_critical_norm_one B
      (cglLemma62CriticalPoint (u - t))
  have hN : ‖(N.value : ℂ) ^ (cglLemma62CriticalPoint u).value‖ =
      (N.value : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_natCast_cpow_of_pos N.positive]
    congr 1
    simp [cglLemma62CriticalPoint]
  unfold cglLemma62FiniteContourIntegrand
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hN, hfunctional, hEuler]
  ring

end

end RHTower
