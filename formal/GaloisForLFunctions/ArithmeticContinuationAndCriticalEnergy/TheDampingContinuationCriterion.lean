import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.ContinuationTransportsAdmission
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.SignedDampingWorkOfTheMobiusEnergy

/-!
# The damping continuation criterion

The programme's headline criterion.  Starting from the *unconditional* endpoint budget at half
damping, a continuation bound on the complete signed work transports admission down to every
positive damping, and cofinal admission is the Riemann hypothesis.

The arithmetic demand is one inequality: for every `0 < a < ½` a nonnegative primitive `β` on
`[a, ½]`, the same for every horizon, with

`−2 Σ_{n ≤ T} A_ε(n) E_ε(n) / (n(n+1)) ≤ β'(ε) · (1 + E_T(ε))`.

Three things are worth stating precisely about this demand.

* It is about the **negative part of one signed number**, not about a norm.  Arbitrarily large
  tangential motion is harmless as long as it does not increase the energy going backwards.
* It **subsumes** the owned tangent-norm receiver: a horizon-uniform bound on the pronic norm of
  the damped Chebyshev tangent is a continuation budget, by Cauchy–Schwarz and `2√E ≤ 1 + E`.  So
  nothing is lost by passing to the signed form, and `TheSignedWorkDemandIsStrictlyWeaker` shows
  something is gained.
* Its deterioration as `a ↓ 0` is unrestricted.  Only finiteness on each compact interval inside
  `(0, ½]` is used; no bound uniform in the damping is required.

The Osgood variant replaces linear control of the loss by any coercive scale, which permits loss
growing faster than linearly in the energy.  Neither variant is proved here: the arithmetic
estimate is the open problem, and these theorems say exactly what would have to be proved.
-/

open Set Filter Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-- The damping derivative of the critical energy, as a family indexed by the horizon. -/
def dampedMobiusEnergyDeriv (T : ℕ) (ε : ℝ) : ℝ := 2 * signedDampingWork ε T

theorem hasDerivAt_dampedMobiusEnergy_deriv {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    HasDerivAt (fun x => dampedMobiusEnergy x T) (dampedMobiusEnergyDeriv T ε) ε :=
  hasDerivAt_dampedMobiusEnergy hε T

/-- **A continuation budget for the damped Möbius energy on `[a, c]`.**  One primitive for all
horizons, paying the negative part of the complete signed work. -/
def DampingContinuation (a c : ℝ) : Prop :=
  LinearContinuation dampedMobiusEnergy dampedMobiusEnergyDeriv a c

/-- **An Osgood continuation budget for the damped Möbius energy on `[a, c]`.** -/
def OsgoodDampingContinuation (a c : ℝ) : Prop :=
  OsgoodContinuation dampedMobiusEnergy dampedMobiusEnergyDeriv a c

/-! ## §1. Transport from the endpoint -/

/-- Continuation from half damping to `a` admits `a`. -/
theorem admits_of_dampingContinuation {a : ℝ} (ha : 0 < a) (hac : a ≤ 1 / 2)
    (h : DampingContinuation a (1 / 2)) : Admits dampedMobiusEnergy a :=
  Admits.of_linearContinuation hac (fun ε _ T => dampedMobiusEnergy_nonneg ε T)
    (fun T ε hε => hasDerivAt_dampedMobiusEnergy_deriv (lt_of_lt_of_le ha hε.1) T) h
    (admits_dampedMobiusEnergy_of_half_le le_rfl)

/-- **The damping continuation criterion for the Riemann hypothesis.**  A horizon-free continuation
budget on every compact interval inside `(0, ½]` gives RH. -/
theorem riemannHypothesis_of_dampingContinuation
    (h : ∀ a : ℝ, 0 < a → a ≤ 1 / 2 → DampingContinuation a (1 / 2)) : RiemannHypothesis :=
  riemannHypothesis_iff_cofinallyAdmits.mpr
    (cofinallyAdmits_of_linearContinuation (by norm_num)
      (fun ε _ T => dampedMobiusEnergy_nonneg ε T)
      (fun T ε hε => hasDerivAt_dampedMobiusEnergy_deriv hε T) h
      (admits_dampedMobiusEnergy_of_half_le le_rfl))

/-- **The Osgood variant.**  Any coercive scale works; linear control of the loss is not
necessary. -/
theorem riemannHypothesis_of_osgoodDampingContinuation
    (h : ∀ a : ℝ, 0 < a → a ≤ 1 / 2 → OsgoodDampingContinuation a (1 / 2)) :
    RiemannHypothesis :=
  riemannHypothesis_iff_cofinallyAdmits.mpr
    (cofinallyAdmits_of_osgoodContinuation (by norm_num)
      (fun ε _ T => dampedMobiusEnergy_nonneg ε T)
      (fun T ε hε => hasDerivAt_dampedMobiusEnergy_deriv hε T) h
      (admits_dampedMobiusEnergy_of_half_le le_rfl))

/-! ## §2. The tangent-norm receiver is a continuation budget -/

/-- **Subsumption.**  A horizon-uniform bound `g` on the pronic norm of the damped Chebyshev
tangent, with a primitive on the interval, *is* a continuation budget.  Cauchy–Schwarz turns the
norm bound into a bound on the signed work and `2√E ≤ 1 + E` puts it in continuation shape. -/
theorem dampingContinuation_of_tangentNorm_le {a c : ℝ} {g β : ℝ → ℝ}
    (hβ : ∀ ε ∈ Icc a c, HasDerivAt β (g ε) ε)
    (hg : ∀ ε ∈ Icc a c, ∀ T : ℕ, pronicNorm T (dampedChebyshevError ε) ≤ g ε) :
    DampingContinuation a c :=
  ⟨β, g, hβ, fun T ε hε =>
    neg_two_mul_signedDampingWork_le_of_tangentNorm_le T (hg ε hε T)⟩

/-- The owned tangent-norm receiver, recovered through the continuation criterion: the integrable
tangent bound is the special case `β(ε) = ∫ g` of the continuation budget. -/
theorem riemannHypothesis_of_tangentNorm_primitive {β g : ℝ → ℝ}
    (hβ : ∀ a : ℝ, 0 < a → a ≤ 1 / 2 → ∀ ε ∈ Icc a (1 / 2 : ℝ), HasDerivAt β (g ε) ε)
    (hg : ∀ ε ∈ Ioc (0 : ℝ) (1 / 2), ∀ T : ℕ,
      pronicNorm T (dampedChebyshevError ε) ≤ g ε) : RiemannHypothesis :=
  riemannHypothesis_of_dampingContinuation fun a ha hac =>
    dampingContinuation_of_tangentNorm_le (hβ a ha hac)
      fun ε hε T => hg ε ⟨lt_of_lt_of_le ha hε.1, hε.2⟩ T

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
