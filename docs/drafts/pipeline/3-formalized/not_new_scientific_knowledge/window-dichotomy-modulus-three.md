# Window viability at fixed modulus is direction-dependent (dichotomy at ‖b‖ = 3)

- **ID:** window-dichotomy-modulus-three
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) - grade **BRIDGE**
- **Source:** two-sided resolution of the small-parameter question; pairs
  `U0WindowObstruction.filledJulia_meets_unit_disk` with a new escape certificate at `b = +3`.
- **Statement:** At the same modulus `3 ∈ (2, 2+√2)`: the filled Julia set of `b = 3` avoids
  the closed unit disk, while the filled Julia set of `b = −3` meets it. No threshold in `‖b‖`
  alone separates window-viable from window-obstructed parameters.

## Goal

The window route (a Böttcher branch analytic on an annulus containing the natural-boundary
circle `|z| = 1` of `u₀`) requires `K_b` to avoid the closed unit disk.  In the ring
`2 < ‖b‖ ≤ 2+√2` this requirement is a *directional* property of `arg b`, proven by a
matched pair of witnesses at one modulus — the first parameter-space-geometry statement in the
tree.  It defines the open object of this lane: the critical curve `ρ(arg b)` separating
viable from obstructed directions, with `ρ(π) = 2+√2` pinned by the obstruction interval
`[−2−√2, −2]` and `ρ(0) < 3` witnessed by `b = 3`.

## Lean surface

- `U0DichotomyWitness.unitDisk_avoids_filledJulia_three` — every `‖z‖ ≤ 1` escapes under
  `z ↦ z² + 3`.
- `U0DichotomyWitness.window_dichotomy_modulus_three` — the conjunction with the `b = −3`
  obstruction; `dichotomy_parameters_same_modulus` records `‖±3‖ = 3`.
- Card: `FullyProvenNewTargets.window_dichotomy_card` (`WindowDichotomyTarget`).
- File: `formal/GaloisForLFunctions/U0/U0DichotomyWitness.lean`.

## Proof shape

Escape chain for `‖z‖ ≤ 1` under `f_3`: the second iterate is `z⁴ + 6z² + 12`, whose real part
is `≥ 12 − 6 − 1 = 5` (numerically the sharp disk minimum is `7`, attained at `z = ±i`); modulus
`≥ 5` lies in the geometric escape regime (`Bottcher.not_mem_filledJulia`), and escape of an
iterate forces escape of the point (`filledJulia_forward`).  The `b = −3` side is the finite
orbit `x₀ ↦ −β ↦ β ↦ β` of the window obstruction.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (proof carried directly in Lean)
- [x] 2 → 3  formalized: axiom set `[propext, Classical.choice, Quot.sound]`; build + lint green
- [ ] 3 → 4  publication-ready

## Log
- 2026-07-02 — witness `b = 3` proven (two-step escape), paired with `b = −3`; registered as
  `window_dichotomy_card`.
- 2026-07-02 — superseded in scope by the critical-curve program: the dichotomy is now a
  bracketed CURVE slice (`critical-curve-slice`, transition at modulus 3 inside
  (155.43°, 155.94°)); ρ(π) = 2+√2 pinned two-sided (`rho_pi_pinned`).
