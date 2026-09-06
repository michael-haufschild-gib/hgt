# Exact constant-speed arithmetic prefix signs

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), [BRIDGE]
- **Module:** `formal/GaloisForLFunctions/RHTower/ArithmeticLinearPhasePrefix.lean`
- **Namespace:** `RHTower.DeletionMixedRefinement`

RH remains unproved. This exact theorem concerns the periodic quadratic at constant phase speed; it does not establish the sign of the logarithmic zeta remainder. No novelty claim is made.

## Theorem and equality classification

Let `b(x)=(fract(x)^2-fract(x))/2` and `H(lambda,A)=integral_(0..A)b(x)sin(lambda*x) dx`. For every `0<lambda<2*pi` and every real `A>=0`, **`H(lambda,A)<=0`** (`linearPhasePrefix_nonpos`).

At `A=2*pi*K/lambda`, for every natural K, put `r=fract(A)`. Then

`H(lambda,A)=r*(1-r)/(2*lambda)-sin(r*lambda/2)*sin((1-r)*lambda/2)/(lambda^2*sin(lambda/2))`.

It is zero **exactly when `r=0`**. Natural floor decomposition covers every endpoint, including K=0 and integer coincidences.

Despite this prefix sign, `integral_(3/2..3)b(x)sin((4*pi/3)*x) dx>0` (`linearPhase_second_turn_pos`). The first turn is negative and the second returns the cumulative prefix exactly to zero.

## Closed proof

Integrate the quadratic on every integer cell against sine, retaining every slope jump and the final fractional cell. A finite trigonometric telescoping sum gives the endpoint formula.

For `0<y<pi`, `(sin y-y cos y)'=y sin y>0`, hence `y cos y<sin y`. Applying this at `r*x` and `(1-r)*x`, with `x=lambda/2`, proves

`x*r*(1-r)*sin x < sin(r*x)*sin((1-r)*x)`

when `0<r<1`. This gives strict negativity away from integer endpoints; the endpoints evaluate to zero. On the first half of each phase turn H decreases; on the second half H increases. Therefore the complete-turn bounds imply nonpositivity at every intermediate cutoff. Subtracting the negative prefix at `3/2` from the zero prefix at `3` proves the positive second turn. No numerical value enters this proof.

## Declarations

Eleven public theorems accompany one definition: `linearPhasePrefix_eq_finite_endpoint`, `linearPhasePrefix_eq_complete_turn`, `phase_endpoint_strict_inequality`, `linearPhasePrefix_complete_turn_neg`, `linearPhasePrefix_complete_turn_nonpos`, `linearPhasePrefix_complete_turn_eq_zero_iff`, `linearPhasePrefix_at_turn`, `linearPhasePrefix_at_turn_nonpos`, `linearPhasePrefix_at_turn_eq_zero_iff`, `linearPhase_second_turn_pos`, and `linearPhasePrefix_nonpos`.

## Validation

Scratch and source `LEAN_NUM_THREADS=1 lake env lean` checks passed without warnings. The serialized leaf audit `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticLinearPhasePrefix` passed, rebuilding only this leaf. The module is wired into `GaloisForLFunctions.RHTower`; no full or umbrella build ran. All twelve public declarations were checked from `/tmp/rh_linear_phase_axioms.lean` and report only `propext`, `Classical.choice`, and `Quot.sound`. The corpus index was refreshed and the new declarations are searchable. `scripts/formal_tools.py lint --check-generated` passed, with existing large-file warnings; output is retained in `/tmp/rh_linear_phase_lint.txt`. All owned Lean and Runpod processes completed.

Related: [frozen conjectures and source gap](../1-in-progress/arithmetic-log-phase-blocks.md), [constant-speed blockwise no-go](../5-failed/arithmetic-linear-block-sign.md), [Runpod report](../2-fully-proven/computations/arithmetic-log-phase-blocks/REPORT.md).
