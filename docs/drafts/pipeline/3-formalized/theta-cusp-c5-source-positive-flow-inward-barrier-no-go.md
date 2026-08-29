# Theta-Cusp C5 Source-Positive Flow Inward-Barrier No-Go

- **ID:** CLG-TTF-C5-source-flow-no-go
- **Stage:** 3-formalized
- **Type:** FALSIFIED / THEOREM (Lean)
- **Source:** Exact completed C5 orientation and slope, source-positive polynomial ODE, and `CLG-TTF-C5-orbit-first-contact`
- **Statement:** Source-positive vector-field dynamics do not make the completed C5 orientation region uniformly forward invariant, even at a positive-mass, positive-gap seam where `U` and `B` velocities are strictly positive.

## RH proof class killed

The attempted shortcut was

`source-positive ODE + positive mass/gap + inward U,B flow`
→ `Lie(Ω) ≥ 0` whenever `Ω=0`
→ no first return of `Ω` to zero
→ `Ω>0` on the positive theta orbit
→ punctured literal completed C5 compensation positivity at every centre
→ local direct fixed-action Jacobian orientation
→ compact/far-tail and rank-four/Ptolemy assembly
→ cofinal no-escape
→ CLG/TTF or Weil positivity
→ RH.

The first implication is false.

## Exact killing theorem

Let `fₙ` be normalized source jets, `pₙ=f₀ⁿ(log F)⁽ⁿ⁾` their division-free
cumulants, and

`Ωc=-p₂²p₇+3p₂p₆p₃+2p₂p₄p₅-4p₄²p₃-18p₂³p₅+36p₂²p₄p₃`.

Lean proves the exact weight-eleven covariant law

`f₀ Lie(Ωc) = Sc + 11 (f₁-(B/2)f₀) Ωc`,

where `Sc` is the already-formalized corrected completed C5 slope. Hence on the orientation
boundary `Ωc=0`, source-positive flow has exactly slope sign after multiplication by source mass.

At algebraic seam `X=100`:

- `Ωc=0`;
- `f₀=Q=47/8>0` and reconstructed gap is positive;
- vector-field velocities satisfy `U'>0`, `B'>0`, and `Q'=0`;
- `Sc<0`, hence `Lie(Ωc)<0`.

Therefore theorem
`not_forall_sourcePositiveC5OrientationBoundary_flow_inward` closes the negation of the proposed
uniform invariant-region implication.

## Strongest positive survivor

The covariant boundary identity is exact and non-trivial:

`Ωc=0 ∧ f₀>0  →  sign Lie(Ωc)=sign Sc`.

It converts every genuine physical-orbit first-contact question into the corpus's explicit
corrected slope, without differentiating high recursive jets. The counterexample proves that
physical theta-orbit incidence or a stronger orbit invariant is logically indispensable; chamber
geometry plus autonomous field direction cannot replace it.

## Novelty audit

- Internal corpus search found exact orientation, exact slope, chart transport, and chamber-only
  no-go, but no covariant Lie identity or uniform-flow counterexample.
- August 2026 literature audit found Jacobi-theta autonomous systems and the current second-level
  concavity proof, but no exact completed C5 orientation, corrected order-eight boundary law, or
  this invariant-region obstruction. Relevant checks: Brezhnev--Lyakhovich--Sharapov,
  arXiv:1012.1429; Planat--Solé, arXiv:2608.19160.

## Lean certificate

- Module:
  `GaloisForLFunctions.HTGeometry.ExactCompletedC5SeamSlopeChamberNoGo`
- Exact law:
  `modularThetaSourcePositive_c5ExactCompletedSeamOrientation_covariantLie`
- Boundary witness:
  `eval_modularThetaSourcePositiveLie_c5ExactCompletedSeamOrientation_hundred_re_neg`
- Flow geometry:
  `modularThetaSourcePositiveVectorField_hundred_seam_geometry`
- Route kill:
  `not_forall_sourcePositiveC5OrientationBoundary_flow_inward`
- Proofs are unconditional and contain no added axioms, hypotheses, `sorry`, `admit`, `opaque`, or
  `unsafe` declarations.

## Gates

- [x] 0 → 1: exact claim, RH passport, and hostile falsifier stated before proof
- [x] 1 → 2: dependency-closed symbolic paper proof
- [x] 2 → 3: Lean theorem closed and targeted module audit green
- [ ] 3 → 4: publication-ready standalone note

## Log

- 2026-08-29 — Exact covariant boundary law proved; uniform source-positive-flow inward barrier
  killed at `X=100`. Physical-orbit first-contact conjecture survives as the sharpened open core.
