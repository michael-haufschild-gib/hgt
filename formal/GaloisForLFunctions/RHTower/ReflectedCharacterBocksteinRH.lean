import GaloisForLFunctions.HTGeometry.RelativeCharacterDerivation
import GaloisForLFunctions.RHTower.GammaCoPoissonIntervalFactorialBridge
import GaloisForLFunctions.RHTower.RiemannComplexModularCharacterLaw

/-!
# Reflected-character Bockstein RH consumer

This file formalizes the exact conditional consumer of the
reflected-character singular-splitting programme.

If a cocycle representing an Xi source-normal Bockstein is non-inner between
the source-inverse and analytic-adjoint characters, commutative
distinct-character splitting forces those characters to coincide. Their
calibrated norms then force the spectral point onto the critical line.

The final theorem states the resulting RH implication with every unproved
source-landing datum exposed as a hypothesis. It does not construct that
landing.
-/

open Complex Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- A nonzero internal carrier on which source-inverse and analytic-adjoint
characters act identically forces its spectral point onto the critical line.
This is the all-degree support consumer; an `Ext` or derived-boundary class
may be used as `x` once its two central actions are proved equal. -/
theorem criticalLine_of_nonzero_reflectedCharacterCarrier
    {A V : Type*} [CommRing A] [Algebra ℂ A]
    [AddCommGroup V] [Module ℂ V]
    (rho : ℂ) (q : A)
    (α β : A →ₐ[ℂ] ℂ) (x : V)
    (hx : x ≠ 0)
    (hcarrier : IsRelativeCharacterCarrier α β x)
    (hsourceInverse :
      ‖α q‖ = Real.exp (1 / 2 - rho.re))
    (hanalyticAdjoint :
      ‖β q‖ = Real.exp (rho.re - 1 / 2)) :
    rho.re = 1 / 2 := by
  have hαβ : α = β :=
    relativeCharacters_eq_of_nonzero_carrier hx hcarrier
  have hexp :
      Real.exp (1 / 2 - rho.re) =
        Real.exp (rho.re - 1 / 2) := by
    rw [← hsourceInverse, ← hanalyticAdjoint, hαβ]
  have harg :
      1 / 2 - rho.re = rho.re - 1 / 2 :=
    Real.exp_injective hexp
  linarith

/-- A non-inner relative cocycle with the source-inverse and
analytic-adjoint norm calibrations forces its spectral point onto the
critical line. -/
theorem criticalLine_of_nonInner_reflectedCharacterDerivation
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (rho : ℂ) (q : A)
    (α β : A →ₐ[ℂ] ℂ) (d : A →ₗ[ℂ] ℂ)
    (hd : IsRelativeCharacterDerivation α β d)
    (houter : ¬ IsInnerRelativeCharacterDerivation α β d)
    (hsourceInverse :
      ‖α q‖ = Real.exp (1 / 2 - rho.re))
    (hanalyticAdjoint :
      ‖β q‖ = Real.exp (rho.re - 1 / 2)) :
    rho.re = 1 / 2 := by
  have hαβ : α = β :=
    relativeCharacters_eq_of_not_inner hd houter
  have hexp :
      Real.exp (1 / 2 - rho.re) =
        Real.exp (rho.re - 1 / 2) := by
    rw [← hsourceInverse, ← hanalyticAdjoint, hαβ]
  have harg :
      1 / 2 - rho.re = rho.re - 1 / 2 :=
    Real.exp_injective hexp
  linarith

/-- **Conditional RH consumer.** If every Xi zero carries a non-inner
source-normal relative cocycle between characters with the exact
source-inverse and analytic-adjoint norm calibrations, then RH holds.

The cocycle, non-innerness, and calibration hypotheses are the explicit
unproved landing interface; none is manufactured in this theorem. -/
theorem riemannHypothesis_of_nonInner_reflectedCharacterBockstein
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (q : A)
    (α β : ℂ → A →ₐ[ℂ] ℂ)
    (d : ℂ → A →ₗ[ℂ] ℂ)
    (hcocycle :
      ∀ rho, xi rho = 0 →
        IsRelativeCharacterDerivation (α rho) (β rho) (d rho))
    (houter :
      ∀ rho, xi rho = 0 →
        ¬ IsInnerRelativeCharacterDerivation (α rho) (β rho) (d rho))
    (hsourceInverse :
      ∀ rho, ‖α rho q‖ = Real.exp (1 / 2 - rho.re))
    (hanalyticAdjoint :
      ∀ rho, ‖β rho q‖ = Real.exp (rho.re - 1 / 2)) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  have hline : rho.re = 1 / 2 :=
    criticalLine_of_nonInner_reflectedCharacterDerivation
      rho q (α rho) (β rho) (d rho)
      (hcocycle rho hzero) (houter rho hzero)
      (hsourceInverse rho) (hanalyticAdjoint rho)
  have hright : 1 / 2 < rho.re := mem_rightHalf.mp hrho
  linarith

/-- **Conditional all-degree RH consumer.** If every Xi zero yields a nonzero
internal class on which the source-inverse and analytic-adjoint characters
induce the same central action, then RH holds.

This exposes the exact derived-diagonal landing premise. It neither defines
an `Ext` group nor asserts that the Gamma/co-Poisson/Sonin Xi conormal supplies
such a class. -/
theorem riemannHypothesis_of_nonzero_reflectedCharacterCarrier
    {A V : Type*} [CommRing A] [Algebra ℂ A]
    [AddCommGroup V] [Module ℂ V]
    (q : A)
    (α β : ℂ → A →ₐ[ℂ] ℂ)
    (x : ℂ → V)
    (hnonzero : ∀ rho, xi rho = 0 → x rho ≠ 0)
    (hcarrier :
      ∀ rho, xi rho = 0 →
        IsRelativeCharacterCarrier (α rho) (β rho) (x rho))
    (hsourceInverse :
      ∀ rho, ‖α rho q‖ = Real.exp (1 / 2 - rho.re))
    (hanalyticAdjoint :
      ∀ rho, ‖β rho q‖ = Real.exp (rho.re - 1 / 2)) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  have hline : rho.re = 1 / 2 :=
    criticalLine_of_nonzero_reflectedCharacterCarrier
      rho q (α rho) (β rho) (x rho)
      (hnonzero rho hzero) (hcarrier rho hzero)
      (hsourceInverse rho) (hanalyticAdjoint rho)
  have hright : 1 / 2 < rho.re := mem_rightHalf.mp hrho
  linarith

end

end RHTower
