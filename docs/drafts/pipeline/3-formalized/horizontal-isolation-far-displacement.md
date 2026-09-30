# Horizontal isolation at every displacement beyond the critical scale

- **ID:** WD-HORIZ-FAR
- **Stage:** 3-formalized
- **Type:** PARTIAL PRODUCER (route WD; consumer of MUST-571 and the Zeta23 horizontal isolation)
- **Parent:** `1-in-progress/rh-goal-loop-opus-2026-09-29.md`, cycle 55
- **STATUS:** MUST-582

## Theorem [L]

`RHTower.exists_horizontallyIsolated_band_le`: for every `ε > 0` there is `B > 0` such that for all
large `T` and every `1 ≤ a` with `2a + 2 ≤ log(4T)`, at least

`(HD(1) − ε)·N(T, 2T) − B (T log(4T) e^{−a/1200}/a + log²(4T))`

simple critical zeros `ρ = ½ + iγ`, `T < γ ≤ 2T`, have every off-line zero with ordinate `γ` at
horizontal distance in `(5/(2 log(T/2π)), 2a/log(4T))` from the critical line
(`N0simpleIsolatedBand`). `HD(1) = 0.6725…` (Montgomery–Taylor constant of Zeta23).

Axioms: `propext, Classical.choice, Quot.sound`.

## Mechanism

- `N0simpleIsolated_le_band_add_far`: the critical zeros isolated at scale `δ` but with a
  same-ordinate off-line partner at distance `≥ Δ` inject into the zeros at distance `≥ Δ` (two
  critical zeros with one ordinate coincide).
- `ncard_farZeros_le`: reflection `ρ ↦ 1 − ρ̄` halves them onto `Re ρ ≥ ½ + Δ`.
- `ncard_rightFarZeros_le`: end strips by Zeta23's local count `N(t, t+1) ≤ A₀ log(|t| + 3)`, the
  middle window by MUST-571 at `U = 4T`.

## Relation to the frontier

WD: "mixed classes displaced farther than `2/(3 log T)` need overlap/leakage control". The
uncontrolled displacement range shrinks from `(5/(2 log(T/2π)), ∞)` to the critical-scale band
`(5/(2 log(T/2π)), 2a/log 4T)` at a cost `O(e^{−a/1200}/a)` of the zeros. Full horizontal isolation
of a positive proportion still needs control inside the band (leakage of the packet inequality at
`εL/2 > arccosh 2`).

Build note: `ZetaFixedSigmaDensity` cannot be imported together with the Zeta23 chain
(`RHTower.integrable_mul_cexp` is defined in both `WindowTransformSamplingParseval` and a module of
the other chain); the multiplicity bound is taken from `zetaZeroConfig.one_le_mult` instead.

## Lean module

`formal/GaloisForLFunctions/RHTower/HorizontallyIsolatedFarDisplacement.lean`; wired after
`HorizontallyIsolatedSimpleZeros`. Clean, `lake build --old` green, no collisions.

## Log
- 2026-09-30 — created and formalized (cycle 55).
