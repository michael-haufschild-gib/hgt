import GaloisForLFunctions.RHTower.DirichletCharacterPrimitiveEulerProduct
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Primitive-conductor transport of Dirichlet `L`-zero multiplicities

The global change-level identity factors an imprimitive nonprincipal Dirichlet
`L`-function into its canonical primitive-conductor `L`-function times a
finite omitted-prime Euler product.  This file proves that product analytic
and nonvanishing throughout the positive half-plane, so the analytic order at
every such point is exactly preserved.

This is the multiplicity-level input required before comparing zero divisors
or zero-density counts across primitive conductor reduction.
-/

open Complex LSeries DirichletCharacter

noncomputable section

namespace RHTower

private theorem cglPrimitiveEulerProduct_analyticAt
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (s : ℂ) :
    AnalyticAt ℂ (cglPrimitiveEulerProduct n χ) s := by
  unfold cglPrimitiveEulerProduct
  apply Finset.analyticAt_fun_prod
  intro p hp
  apply AnalyticAt.sub
  · exact analyticAt_const
  · apply AnalyticAt.mul
    · exact analyticAt_const
    · apply AnalyticAt.cpow analyticAt_const analyticAt_id.neg
      exact Complex.natCast_mem_slitPlane.mpr
        (Nat.prime_of_mem_primeFactors hp).ne_zero

private theorem cglPrimitiveLFunction_analyticAt
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (s : ℂ) :
    AnalyticAt ℂ (cglPrimitiveLFunction n χ) s := by
  unfold cglPrimitiveLFunction
  letI : NeZero (cglPrimitiveCharacterReduction n χ).conductor :=
    ⟨Nat.ne_of_gt (cglPrimitiveCharacterReduction n χ).conductor_pos⟩
  exact (DirichletCharacter.differentiable_LFunction
    (cglPrimitiveCharacterReduction n χ).nonprincipal).analyticAt s

/-- In the positive half-plane, canonical primitive-conductor reduction
preserves the analytic order of every nonprincipal Dirichlet `L`-function. -/
theorem cglPrimitiveLFunction_analyticOrderAt_eq_input
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (s : CGLPositiveRealPartPoint) :
    analyticOrderAt (cglPrimitiveLFunction n χ) s.1 =
      analyticOrderAt (DirichletCharacter.LFunction χ.1) s.1 := by
  have hinput : DirichletCharacter.LFunction χ.1 =
      fun w => cglPrimitiveLFunction n χ w * cglPrimitiveEulerProduct n χ w := by
    funext w
    exact cglPrimitiveLFunction_changeLevel n χ w
  rw [hinput]
  change analyticOrderAt (cglPrimitiveLFunction n χ) s.1 =
    analyticOrderAt ((cglPrimitiveLFunction n χ) *
      (cglPrimitiveEulerProduct n χ)) s.1
  rw [analyticOrderAt_mul
    (cglPrimitiveLFunction_analyticAt n χ s.1)
    (cglPrimitiveEulerProduct_analyticAt n χ s.1),
    (cglPrimitiveEulerProduct_analyticAt n χ s.1).analyticOrderAt_eq_zero.mpr
      (cglPrimitiveEulerProduct_ne_zero n χ s), add_zero]

end RHTower
