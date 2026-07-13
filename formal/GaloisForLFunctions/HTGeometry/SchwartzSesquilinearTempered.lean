import GaloisForLFunctions.HTGeometry.SchwartzSesquilinear
import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Currying continuous Schwartz forms into tempered distributions

A jointly continuous complex sesquilinear form on Schwartz space gives, after fixing its second
argument, an actual continuous linear functional and hence a tempered distribution.  Momentum
symmetry becomes the derivative intertwining law on this family, while simultaneous translation
invariance becomes contragredient translation covariance.

This is the first formal interface needed for the missing Bochner--Schwartz converse for positive
translation-invariant Schwartz forms.
-/

open Complex Function Filter
open scoped SchwartzMap Topology

noncomputable section

namespace SchwartzMap.ContinuousSchwartzSesquilinearForm

/-- The continuous linear functional obtained by fixing the second argument of a continuous
Schwartz sesquilinear form. -/
def leftFunctional (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (v : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ →L[ℂ] ℂ where
  toFun u := Q u v
  map_add' u w := Q.map_add_left u w v
  map_smul' c u := Q.map_smul_left c u v
  cont := Q.continuous.comp (continuous_id.prodMk continuous_const)

@[simp] theorem leftFunctional_apply
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (u v : SchwartzMap ℝ ℂ) : Q.leftFunctional v u = Q u v := rfl

/-- The fixed-second-argument functional as a genuine tempered distribution. -/
def leftTemperedDistribution
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (v : SchwartzMap ℝ ℂ) : TemperedDistribution ℝ ℂ :=
  ContinuousLinearMap.toPointwiseConvergenceCLM _ _ _ _ (Q.leftFunctional v)

@[simp] theorem leftTemperedDistribution_apply
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (u v : SchwartzMap ℝ ℂ) : Q.leftTemperedDistribution v u = Q u v := rfl

/-- Momentum symmetry is exactly the derivative-intertwining law for the curried tempered
distribution family. -/
theorem leftFunctional_deriv
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hMomentum : Q.MomentumSymmetric)
    (u v : SchwartzMap ℝ ℂ) :
    Q.leftFunctional v ((-I) • derivCLM ℂ ℂ u) =
      Q.leftFunctional ((-I) • derivCLM ℂ ℂ v) u := by
  exact hMomentum u v

/-- Momentum symmetry transports a translation in the test argument to the inverse translation
in the parameter argument. -/
theorem leftFunctional_translate
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hMomentum : Q.MomentumSymmetric)
    (u v : SchwartzMap ℝ ℂ) (a : ℝ) :
    Q.leftFunctional v (translateCLM ℂ a u) =
      Q.leftFunctional (translateCLM ℂ (-a) v) u := by
  rw [leftFunctional_apply, leftFunctional_apply]
  have h := Q.translate_pair_invariant hMomentum u (translateCLM ℂ (-a) v) a
  simpa using h

end SchwartzMap.ContinuousSchwartzSesquilinearForm
