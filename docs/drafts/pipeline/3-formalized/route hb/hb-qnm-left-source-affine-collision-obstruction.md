# Self-source-zero obstruction to an HB QNM extinction bridge

- **ID:** HB-CQ-LS-SS0
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** ../1-in-progress/rh-current-frontier-map.md · HB literal QNM-value/extinction edge
- **Statement:** At any strict-right `q : XiZeroCopy` with `physicalSelfSourceCoefficient q = 0`, canonical QNM value is zero while every unit canonical left source at `q` is nonzero.

## Goal

Kill the exact pointwise receiver bridge `canonicalQNMValue = 0 ↔ unit-left-source = 0` whenever its literal self-source vanishes. This isolates a necessary pure-Xi affine-no-collision theorem for any surviving HB zero-equivalence route.

## Gates

- [x] 0 → 1  in-progress: source-pure and well-typed.
- [x] 1 → 2  fully-proven: complete paper proof below, conditional only on displayed Xi collision.
- [x] 2 → 3 formalized: unconditional Lean proof (see "Formalized (2026-09-27)").
- [ ] 3 → 4  publication-ready.

## Proof `[PROVED HERE]`

Let `q` be strict-right and assume `physicalSelfSourceCoefficient q = 0`. HB-CQ-SS0 gives
`canonicalQNMValue q br side amp = 0` for arbitrary literal `br`, `side`, and `amp`.

For every overtone `n`, the existing canonical-left classification gives
`hbXiPeierlsMinusLeftSource n 1 q = 0 ↔ Re q = 1/2`; its right side is false by strict-rightness.
Thus that left source is nonzero. The claimed zero/nonzero separation follows. In the strict-right chamber,
`physicalSelfSourceCoefficient_zero_iff_xi` specializes the premise to
`xi(5q/2-1)=0 ∨ xi(q/2)=0 ∨ xi(3q/2)=0`.

## Whole-route consequence

This does **not** exhibit a collision and therefore does not retire HB. It proves a sharp fork:

- any of the three affine collisions at one strict-right Xi occurrence kills every pointwise QNM-zero ↔ unit-left-extinction bridge; or
- a route using that bridge must prove the new affine no-collision premise
  `physicalSelfSourceCoefficient q ≠ 0` on strict-right Xi support.

The five-halves orbit classification reduces failure of this no-collision premise to a `Re=3/5` landing or an all-zero orbit trapped in `[8/15,2/3]`; neither alternative is resolved.

## Lean target

`RHTower.canonicalQNMValue_zero_ne_unitLeftSource_of_physicalSelfSourceCoefficient_eq_zero`

Dependencies: `canonicalQNMValue_eq_zero_of_physicalSelfSourceCoefficient_eq_zero` and
`hbXiPeierlsMinusLeftSource_eq_zero_iff`.

## Formalized (2026-09-27)

`RHTower.canonicalQNMValue_zero_ne_unitLeftSource_of_physicalSelfSourceCoefficient_eq_zero`
(`ThetaCuspHawkingBMCanonicalQNMSelfSourceZero.lean`): for strict-right `q` with
`physicalSelfSourceCoefficient q = 0`, every canonical QNM value is zero, every unit canonical
left source `hbXiPeierlsMinusLeftSource n 1 q` and `hbXiPeierlsPlusLeftSource n 1 q` is nonzero,
and `ξ(5q/2-1) = 0 ∨ ξ(q/2) = 0 ∨ ξ(3q/2) = 0`.  The killed bridge is stated separately:
`not_canonicalQNMValue_eq_zero_iff_unitLeftSource_eq_zero`.  The cited dependency is
`hbXiPeierlsMinusLeftSource_eq_zero_iff` (with its `Plus` companion).  Axioms
`[propext, Classical.choice, Quot.sound]`.
