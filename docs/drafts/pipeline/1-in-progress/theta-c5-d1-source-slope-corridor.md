# Theta C5--D1 source slope corridor

- **ID:** theta-c5-d1-source-slope-corridor
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** full-corpus weld of exact completed C5 and TCD D1
- **Statement:** Prove on every actual theta-source point `u>0` that `0<Ω'(u)` and `L(u)Ω'(u)<R₇(u)`.

## Goal

One source law closes two shared RH gates: exact completed C5 orientation and reflected eighth-order D1 positivity. Static jet-space implication is impossible; producer must use actual theta-orbit dynamics.

## Gates

- [x] 0 → 1 in-progress: exact source-pure corridor and two-gate closure formalized
- [ ] 1 → 2 fully-proven: global actual-source corridor
- [ ] 2 → 3 formalized: unconditional global corridor theorem
- [ ] 3 → 4 publication-ready

## Exact weld

Let `A=-K₂`, `B=-K₄`, `C=-K₆`, `D=-K₈`, `L=4A²-B`, `Ω'` be exact C5 orientation slope, and `P` the D1 polynomial. Lean proves

`A² P + L Ω' = R₇(A,B,C,E,F,G)`,

where `R₇` contains no eighth jet `D`. Since actual source has `A>0` and `L>0`, corridor's upper wall gives `P>0`; lower wall integrates from `Ω(0)=0` to `Ω(u)>0`.

## Lean status

- Module: `RHTower/ThetaCuspExactCompletedC5D1SlopeCorridor.lean`
- Identity: `thetaCuspC5D1SlopeReserve_identity`
- Local source law: `eventually_right_thetaCuspC5D1SlopeCorridorAt`
- Two-gate closure: `thetaCuspC5_D1_closed_of_slopeCorridor`
- Direct check and target-module build pass; axioms only `propext`, `Classical.choice`, `Quot.sound`.

## Checked locks

- `ExactCompletedC5D1StaticWeldNoGo`: source-positive seam counterstate kills static D1→C5 slope/orientation transfer.
- `ExactCompletedC5SeamSlopeChamberNoGo`, `ExactCompletedC5AdaptedPhysicalConeNoGo`, `ExactCompletedC5RefinedParabolicConeNoGo`: finite static C5 chambers fail.
- TCD finite/infinite contravariant-carrier no-gos: generic Hankel/operator transport cannot prove actual D1.

## Open core

Prove corridor from an independent actual-source invariant, not from desired C5 and D1 signs. Global corridor premise is currently a compression of two gates, not yet a producer. Surviving edge: theta-source orbit dynamics. Local corridor is unconditional; D1 already known for `u≥137/2000`, so only compact C5 sign and D1 interval `0<u<137/2000` matter.

## Log

- 2026-09-02 — exact eighth-jet cancellation, local corridor, and conditional two-gate closure proved in Lean.
