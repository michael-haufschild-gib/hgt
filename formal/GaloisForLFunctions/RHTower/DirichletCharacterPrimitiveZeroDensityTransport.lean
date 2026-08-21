import GaloisForLFunctions.RHTower.DirichletCharacterPrimitiveZeroMultiplicity
import GaloisForLFunctions.RHTower.DirichletLZeroDensityVerticalWindow

/-!
# Primitive-conductor transport of positive zero-density windows

This file attaches canonical primitive-conductor reduction to the corpus's
literal centered zero-density divisors.  A positive-abscissa window is carried
as certified data.  Inside every such window, the original completed Dirichlet
`L`-function and its primitive-conductor completed `L`-function have exactly
the same divisor multiplicity at every point, and hence exactly the same
finsum zero count.

The result is characterwise.  Reindexing all characters at an ambient modulus
into the corresponding primitive conductor families is a separate finite
injection and summation step.
-/

open Complex Metric

noncomputable section

namespace RHTower

/-- A centered Dirichlet zero-density window whose left boundary is certified
to lie in the positive half-plane. -/
structure CGLPositiveZeroDensityVerticalWindow where
  sigma : ℝ
  sigma_pos : 0 < sigma
  center : ℝ
  halfWidth : NNReal

/-- The literal centered window carried by certified positive parameters. -/
def CGLPositiveZeroDensityVerticalWindow.carrier
    (W : CGLPositiveZeroDensityVerticalWindow) : Set ℂ :=
  cglZeroDensityVerticalWindow W.sigma W.center W.halfWidth

/-- A point certified to belong to a positive zero-density window.  Membership
is data rather than a raw caller premise. -/
structure CGLPositiveZeroDensityVerticalWindowPoint
    (W : CGLPositiveZeroDensityVerticalWindow) where
  value : ℂ
  within : value ∈ W.carrier

private theorem cglPrimitiveCompletedLFunction_analyticOnNhd
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    AnalyticOnNhd ℂ (cglPrimitiveCompletedLFunction n χ) Set.univ := by
  unfold cglPrimitiveCompletedLFunction
  letI : NeZero (cglPrimitiveCharacterReduction n χ).conductor :=
    ⟨Nat.ne_of_gt (cglPrimitiveCharacterReduction n χ).conductor_pos⟩
  exact (DirichletCharacter.differentiable_completedLFunction
    (cglPrimitiveCharacterReduction n χ).nonprincipal).differentiableOn.analyticOnNhd isOpen_univ

/-- At every certified point of a positive centered window, primitive
conductor reduction preserves the exact completed-`L` divisor multiplicity. -/
theorem cglPrimitiveCompletedLFunction_divisor_eq_input_at_windowPoint
    (n : ℕ) (χ : NonprincipalDirichletCharacter n)
    (W : CGLPositiveZeroDensityVerticalWindow)
    (z : CGLPositiveZeroDensityVerticalWindowPoint W) :
    MeromorphicOn.divisor (cglPrimitiveCompletedLFunction n χ) W.carrier z.value =
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.1) W.carrier z.value := by
  have hzwindow : z.value ∈ cglZeroDensityVerticalWindow W.sigma W.center W.halfWidth := z.within
  let hzpos : CGLPositiveRealPartPoint :=
    ⟨z.value, lt_of_lt_of_le W.sigma_pos hzwindow.1⟩
  have horder := cglPrimitiveCompletedLFunction_analyticOrderAt_eq_input n χ hzpos
  dsimp only [hzpos] at horder
  have hprimitive := cglPrimitiveCompletedLFunction_analyticOnNhd n χ
  have hinput := completedLFunction_analyticOnNhd n χ
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
      (hprimitive.mono (Set.subset_univ W.carrier)) z.within,
    MeromorphicOn.AnalyticOnNhd.divisor_apply
      (hinput.mono (Set.subset_univ W.carrier)) z.within]
  exact congrArg (fun order : ℕ∞ => (ENat.map Nat.cast order).untop₀) horder

/-- The multiplicity-weighted centered-window zero count of the primitive
conductor completed function. -/
def cglPrimitiveCompletedLFunctionZeroDensityVerticalWindowCount
    (n : ℕ) (χ : NonprincipalDirichletCharacter n)
    (W : CGLPositiveZeroDensityVerticalWindow) : ℝ :=
  (↑(∑ᶠ z, MeromorphicOn.divisor (cglPrimitiveCompletedLFunction n χ) W.carrier z) : ℝ)

/-- Canonical primitive-conductor reduction preserves the literal
multiplicity-weighted zero count in every certified positive centered window. -/
theorem cglPrimitiveCompleted_zeroDensityVerticalWindowCount_eq_input
    (n : ℕ) (χ : NonprincipalDirichletCharacter n)
    (W : CGLPositiveZeroDensityVerticalWindow) :
    cglPrimitiveCompletedLFunctionZeroDensityVerticalWindowCount n χ W =
      completedLFunctionZeroDensityVerticalWindowCount n χ W.sigma W.center W.halfWidth := by
  have hdiv : MeromorphicOn.divisor (cglPrimitiveCompletedLFunction n χ) W.carrier =
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.1) W.carrier := by
    ext z
    by_cases hz : z ∈ W.carrier
    · exact cglPrimitiveCompletedLFunction_divisor_eq_input_at_windowPoint n χ W ⟨z, hz⟩
    · simp only [MeromorphicOn.divisor_def, hz, and_false, ite_false]
  unfold cglPrimitiveCompletedLFunctionZeroDensityVerticalWindowCount
    completedLFunctionZeroDensityVerticalWindowCount
  change (↑(∑ᶠ z, MeromorphicOn.divisor (cglPrimitiveCompletedLFunction n χ) W.carrier z) : ℝ) =
    (↑(∑ᶠ z, MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.1) W.carrier z) : ℝ)
  rw [hdiv]

end RHTower
