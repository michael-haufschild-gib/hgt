import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.ContinuationTransportsAdmission
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.SignedDampingWorkOfTheMobiusEnergy
import GaloisForLFunctions.BezoutValuationIncidence.LittlewoodAdmitsTheReceiverAboveHalfTheZeroAbscissa

/-!
# The damping continuation criterion

The programme's headline criterion.  Starting from an admitted damping, a continuation bound on
the complete signed work transports admission downwards, and admission at dampings accumulating at
zero is the Riemann hypothesis.

The arithmetic demand is one inequality: for every `0 < a < c` a primitive `β` on `[a, c]`, the
same for every horizon, with

`−2 Σ_{n ≤ T} A_ε(n) E_ε(n) / (n(n+1)) ≤ β'(ε) · (1 + E_T(ε))`.

Four things are worth stating precisely about it.

* It constrains the **negative part of one signed number**, not a norm.  Arbitrarily large
  tangential motion is harmless as long as it does not increase the energy going backwards.
* It **subsumes** the owned tangent-norm receiver, by Cauchy–Schwarz and `2√E ≤ 1 + E`.  So
  nothing is lost by passing to the signed form, and `TheSignedWorkDemandIsStrictlyWeaker` shows
  something is gained.
* The endpoint is **any** admitted damping.  Half damping is unconditional, and so is every
  damping above half the zero abscissa, so the interval the continuation has to cross is
  `(0, Θ/2]` and not `(0, ½]`.
* Continuation **need not reach zero to produce a theorem**: a budget available only on `[a, c]`
  for `a` in `(a₀, c]` already bounds the zero abscissa by `½ + a₀`.  That is the programme's
  non-RH deliverable, and it is a genuine zero-free strip, not a change of coordinates.

Deterioration of the budget as `a ↓ 0` is unrestricted: only finiteness on each compact interval
is used.  Nothing here proves the arithmetic estimate; these theorems say exactly what would have
to be proved, and what a partial proof already buys.
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

/-! ## §1. Transport from an arbitrary admitted endpoint -/

/-- Continuation from an admitted `c` down to `a` admits `a`. -/
theorem admits_of_dampingContinuation {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hadm : Admits dampedMobiusEnergy c) (h : DampingContinuation a c) :
    Admits dampedMobiusEnergy a :=
  Admits.of_linearContinuation hac (fun ε _ T => dampedMobiusEnergy_nonneg ε T)
    (fun T ε hε => hasDerivAt_dampedMobiusEnergy_deriv (lt_of_lt_of_le ha hε.1) T) h hadm

/-- **The damping continuation criterion for the Riemann hypothesis.**  A horizon-free continuation
budget on every compact interval inside `(0, c]`, for one admitted `c`, gives RH. -/
theorem riemannHypothesis_of_dampingContinuation_endpoint {c : ℝ} (hc : 0 < c)
    (hadm : Admits dampedMobiusEnergy c)
    (h : ∀ a : ℝ, 0 < a → a ≤ c → DampingContinuation a c) : RiemannHypothesis :=
  riemannHypothesis_iff_cofinallyAdmits.mpr
    (cofinallyAdmits_of_linearContinuation hc (fun ε _ T => dampedMobiusEnergy_nonneg ε T)
      (fun T ε hε => hasDerivAt_dampedMobiusEnergy_deriv hε T) h hadm)

/-- **The Osgood variant.**  Any coercive scale works; linear control of the loss is not
necessary. -/
theorem riemannHypothesis_of_osgoodDampingContinuation_endpoint {c : ℝ} (hc : 0 < c)
    (hadm : Admits dampedMobiusEnergy c)
    (h : ∀ a : ℝ, 0 < a → a ≤ c → OsgoodDampingContinuation a c) : RiemannHypothesis :=
  riemannHypothesis_iff_cofinallyAdmits.mpr
    (cofinallyAdmits_of_osgoodContinuation hc (fun ε _ T => dampedMobiusEnergy_nonneg ε T)
      (fun T ε hε => hasDerivAt_dampedMobiusEnergy_deriv hε T) h hadm)

/-! ## §2. The unconditional endpoints -/

/-- Continuation from half damping, the unconditional endpoint of the family. -/
theorem riemannHypothesis_of_dampingContinuation
    (h : ∀ a : ℝ, 0 < a → a ≤ 1 / 2 → DampingContinuation a (1 / 2)) : RiemannHypothesis :=
  riemannHypothesis_of_dampingContinuation_endpoint (by norm_num)
    (admits_dampedMobiusEnergy_of_half_le le_rfl) h

theorem riemannHypothesis_of_osgoodDampingContinuation
    (h : ∀ a : ℝ, 0 < a → a ≤ 1 / 2 → OsgoodDampingContinuation a (1 / 2)) : RiemannHypothesis :=
  riemannHypothesis_of_osgoodDampingContinuation_endpoint (by norm_num)
    (admits_dampedMobiusEnergy_of_half_le le_rfl) h

/-- **The interval to cross is `(0, Θ/2]`.**  Littlewood's bound already admits every damping
above half the zero abscissa, so the continuation obligation may start there instead of at `½`.
This shortens the interval the arithmetic estimate has to cover by `½ − Θ/2`. -/
theorem riemannHypothesis_of_dampingContinuation_above_half_abscissa {c : ℝ}
    (hc1 : zetaZeroAbscissa / 2 < c) (hc2 : c ≤ 1 / 2)
    (h : ∀ a : ℝ, 0 < a → a ≤ c → DampingContinuation a c) : RiemannHypothesis :=
  riemannHypothesis_of_dampingContinuation_endpoint
    (lt_trans (by linarith [zetaZeroAbscissa_pos]) hc1)
    (mem_receiverDampings_of_half_zetaZeroAbscissa_lt hc1 hc2).2 h

/-! ## §3. Partial continuation is a zero-free strip -/

/-- **Partial continuation gives a quantitative zero-free strip.**  If the budget exists on
`[a, c]` for every `a` in `(a₀, c]`, every damping of `(a₀, c)` is admitted, the admissible
dampings accumulate at `a₀`, and the zero abscissa is at most `½ + a₀`.  Continuation does not
have to reach zero to prove something new. -/
theorem zetaZeroAbscissa_le_half_add_of_partial_dampingContinuation {a₀ c : ℝ} (ha₀ : 0 ≤ a₀)
    (ha₀c : a₀ < c) (hadm : Admits dampedMobiusEnergy c)
    (h : ∀ a : ℝ, a₀ < a → a ≤ c → DampingContinuation a c) :
    zetaZeroAbscissa ≤ 1 / 2 + a₀ := by
  refine zetaZeroAbscissa_le_of_accPt_receiverDampings (accPt_of_Ioo_subset ha₀c ?_)
  intro a ha
  have ha0 : 0 < a := lt_of_le_of_lt ha₀ ha.1
  exact (mem_receiverDampings_iff_admits ha0).mpr
    (admits_of_dampingContinuation ha0 (le_of_lt ha.2) hadm (h a ha.1 (le_of_lt ha.2)))

/-! ## §4. The tangent-norm receiver is a continuation budget -/

/-- **Subsumption.**  A horizon-uniform bound `g` on the pronic norm of the damped Chebyshev
tangent, with a primitive on the interval, *is* a continuation budget.  Cauchy–Schwarz turns the
norm bound into a bound on the signed work and `2√E ≤ 1 + E` puts it in continuation shape. -/
theorem dampingContinuation_of_tangentNorm_le {a c : ℝ} {g β : ℝ → ℝ}
    (hβ : ∀ ε ∈ Icc a c, HasDerivAt β (g ε) ε)
    (hg : ∀ ε ∈ Icc a c, ∀ T : ℕ, pronicNorm T (dampedChebyshevError ε) ≤ g ε) :
    DampingContinuation a c :=
  ⟨β, g, hβ, fun T ε hε =>
    neg_two_mul_signedDampingWork_le_of_tangentNorm_le T (hg ε hε T)⟩

/-- The owned tangent-norm receiver, recovered through the continuation criterion. -/
theorem riemannHypothesis_of_tangentNorm_primitive {β g : ℝ → ℝ}
    (hβ : ∀ a : ℝ, 0 < a → a ≤ 1 / 2 → ∀ ε ∈ Icc a (1 / 2 : ℝ), HasDerivAt β (g ε) ε)
    (hg : ∀ ε ∈ Ioc (0 : ℝ) (1 / 2), ∀ T : ℕ,
      pronicNorm T (dampedChebyshevError ε) ≤ g ε) : RiemannHypothesis :=
  riemannHypothesis_of_dampingContinuation fun a ha hac =>
    dampingContinuation_of_tangentNorm_le (hβ a ha hac)
      fun ε hε T => hg ε ⟨lt_of_lt_of_le ha hε.1, hε.2⟩ T

/-! ## §5. What a continuation budget forces on the Markov face -/

/-- **Backward continuation must pay the jump energy.**  Through the Markov face of the same
derivative, a continuation budget bounds the nonnegative jump energy of the arithmetic chain by
the boundary flux, less the density forcing, plus the budget.  So the dissipation of the chain is
an obstruction to backward continuation, not an aid to it. -/
theorem arithmeticDampingTotalJumpEnergy_le_of_continuation_bound {ε b : ℝ} (hε : 0 < ε) (T : ℕ)
    (hb : -(2 * signedDampingWork ε T) ≤ b) :
    arithmeticDampingTotalJumpEnergy (arithmeticDampingCenteredMean ε) T ≤
      arithmeticDampingBoundaryFlux (arithmeticDampingCenteredMean ε) T -
        2 * dampedReadout ε *
          (∑ n ∈ Icc 1 T, ((n : ℝ) / (n + 1)) * arithmeticDampingCenteredMean ε n) + b := by
  have h := two_mul_signedDampingWork_eq_markov hε T
  linarith

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
