# Exponentially few critical-scale right discs fail to contract

- **ID:** TG-DISC-EXP
- **Stage:** 3-formalized
- **Type:** PARTIAL PRODUCER (route TG consumer of MUST-571)
- **Parent:** `1-in-progress/rh-goal-loop-opus-2026-09-29.md`, cycle 53
- **STATUS:** MUST-578

## Theorem [L]

`RHTower.exists_criticalScale_badDisc_exponential_le`: there is `B > 0` such that for all large `U`
one pair of heights `T₁ ∈ (U/4, U/4 + 1)`, `T₂ ∈ (U/2 − 1, U/2)` serves every radius: for all
`1 ≤ a` with `2a + 2 ≤ log U` and `16a ≤ log U`, among the discs of radius `r = 2a/log U` centred at
`½ + 2r + 3rk·i` with heights in `[T₁, T₂]`, the discs containing a zero of `ξ` number at most
`B e^{−a/1200}` times all discs. Off those discs the adjoint seam of the `ξ` phase is a strict
contraction (`criticalScaleDisc_adjointSeam_lt_one`). `B = 6A/π + 1` with `A` from MUST-571.

Axioms: `propext, Classical.choice, Quot.sound`.

## Mechanism

Every exceptional disc contains a zero with `Re ρ ≥ ½ + r`, different discs different zeros
(`card_badCriticalScaleWindowDiscs_le`); MUST-571 at the same `a` bounds those zeros by
`(log U/(2πa))((T₂−T₁)A e^{−a/1200} + K log U)`; the window has at least `(T₂−T₁)log U/(6a) − 2`
discs. The `K log U` and `−2` terms are absorbed because `e^{−a/1200} ≥ U^{−1/2400}`.

## Relation to the frontier

Replaces the qualitative "for every ε, large fixed a gives bad fraction ≤ ε"
(`exists_criticalScale_badDisc_proportion_le`) by an exponential rate uniform in `a`. The bad
fraction at fixed `a` is still not shown to be `o(1)`: that is the statement that the zeros with
`β − ½ ≥ 2a/log T` are `o(N(T))` for fixed `a`, which is open (it would follow from a mollified mean
square `1 + o(1)` at `σ = ½ + a/log T`).

## Lean module

`formal/GaloisForLFunctions/RHTower/XiCriticalScaleDiscSeamExponentialDensity.lean`
(`badDisc_exponential_arith`, `exists_criticalScale_badDisc_exponential_le`); wired after
`XiSliceBoundedOrderDensity`. Clean, `lake build --old` green, no collisions.

## Log
- 2026-09-30 — created and formalized (cycle 53).
