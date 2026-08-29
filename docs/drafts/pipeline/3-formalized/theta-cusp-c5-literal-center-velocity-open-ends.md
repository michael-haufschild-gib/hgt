# Theta C5 literal center-velocity open ends

- **ID:** C5-VP1-literal-velocity-open-ends
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `../1-in-progress/theta-cusp-c5-center-velocity-likelihood-bregman-cone.md`
- **Statement:** Literal modular-center C5 velocity is strictly positive near the seam and on a
  cofinal tail; its global positivity is exactly one compact-annulus problem.

## Goal

Discharge both noncompact premises in

`global literal center velocity → modular-center C5 → fixed-action/higher-packet transport →
no escape → CLG/TTF or Weil polarization positivity → RH`.

## Gates

- [x] 0 → 1 in-progress: corpus-derived normalized-tail conjecture and hostile falsifiers recorded
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: unconditional Lean theorem, umbrella wired, targeted audit green
- [ ] 3 → 4 publication-ready: standalone exposition and external review

## Paper proof

Write `S(t)` for the first-atom reflection scale,
`r(t)=exp(thetaCuspReflectedLogAction 0 t)-1`, and `q₁,q₂,q₃` for the first three center reflected
log jets. Exact first-atom likelihood factorization and spectral-tail cooling give

`q₁/S → 4`, `q₂/S → 8`, `q₃/S → 16`.

The action lower bound `19t²-t < action(t)` implies `r(t)→∞`. Also `t,S→∞`. Divide the literal
action velocity by the positive scale `r*t²*S³`. Expanding its exact polynomial shows every term
contains one of `1/t`, `1/S`, or `1/r`, except

`5 * (q₁/S)³ → 5 * 4³ = 320`.

The normalized action core therefore tends to `320`, so both action core and literal source
velocity are eventually strictly positive.

For the seam, let `W` be the generic fifth-root divided-drop curvature numerator of the center
reflected product. Even smoothness gives all jets below eight equal to zero; the strict completed
second--sixth Hankel margin gives `W⁽⁸⁾(0)>0`. Continuity and repeated derivative monotonicity
yield `W'(t)>0` for all sufficiently small `t>0`. The exact derivative identity identifies `W'`
with literal center velocity.

Combining both endpoint chambers and shrinking the seam radius against a positive tail threshold
gives qualitative `0<delta≤T` with

`global velocity positivity ↔ velocity positivity on [delta,T]`.

`[PROVED HERE]`

## Proof-burden reduction

- **Discharged premise:** strict literal center velocity on a punctured modular-seam chamber.
- **Discharged premise:** strict literal center velocity on a cofinal physical tail.
- **Strongest survivor:** exact compact-annulus equivalence for global literal center velocity.
- **Remaining open core:** prove strict velocity positivity on that compact annulus, then complete
  center-C5 integration and the off-center/higher-packet joins.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureVelocityFarTail`
- Main asymptotic:
  `tendsto_thetaCuspCenterFifthRootVelocityActionCore_normalized`
- Endpoint signs:
  `exists_thetaCuspReflectedSourceFifthRootCurvatureVelocity_zero_pos_right`,
  `eventually_thetaCuspReflectedSourceFifthRootCurvatureVelocity_zero_pos`
- Exact reduction:
  `exists_thetaCuspReflectedSourceFifthRootCurvatureVelocity_zero_compactCore`

## Novelty audit

Internal corpus search found no literal center-velocity tail limit, seam chamber, or compact-core
equivalence. Existing results treated the C5 numerator and completed seam orientation, not its
literal displacement derivative. Primary-literature search through August 2026 found
Planat--Solé, *Second-Level Concavity of the Riemann Xi Kernel* (arXiv:2608.19160), including a
first-summand tail method, but no fifth-root divided-drop velocity theorem or coefficient `320`.

## Log

- 2026-08-29 — conjectured from exact corpus likelihood and log-jet tail laws
- 2026-08-29 — paper proof closed; seam and cofinal tail formalized; compact reduction proved
