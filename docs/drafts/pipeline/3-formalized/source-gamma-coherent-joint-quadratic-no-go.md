# Coherent joint quadratic source/Gamma scalarization no-go

- **ID:** SG-CJQ-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `SourceGammaChannelResolvedNaturalityNoGo` + `SourceGammaChannelPositiveHermitianScalarizationNoGo`
- **Statement:** Every fixed complex quadratic observable on the coherent pair of genuine prime-2/prime-3 source-boundary outputs is identically blind or has zero locus exactly `t = 0`.

## Goal

Killed chain class
`fixed coherent cross-boundary quadratic mixing → cross-prime leak extinction → shared HB/FZZ-P/PW-B/RBH Ward → RH`.

## Gates

- [x] 0 → 1: corpus-derived, source-pure, exact attack
- [x] 1 → 2: dependency-closed rank-one compression proof
- [x] 2 → 3: Lean certificate, targeted build, standard axioms, umbrella
- [ ] 3 → 4: publication-ready

## Approach

Actual outputs `(0,d(t))`, `(-d(t),0)` flatten to `d(t)·(0,1,-1,0)`. Every fixed `4×4` complex quadratic form is `κ(A)·normSq(d(t))`, with `κ(A)=Re(A₁₁-A₁₂-A₂₁+A₂₂)`.

## No-go closure

- **Exact killing theorem/mechanism:** `sharedWardCoherentJointQuadraticScalarizationRouteKilled`; `κ=0` is blind, `κ≠0` is exactly shared Ward/RH.
- **Strongest positive survivor:** exact rank-one invariant `κ(A)`.
- **New insight:** positivity, Hermiticity, channel separation, and absence of cross-boundary interference are unnecessary; viable dynamics must add an independent source feature, be genuinely nonlinear/source-adaptive, or force `d(t)=0` itself.
- **Status:** direct Lean PASS; targeted module build PASS; axioms `propext`, `Classical.choice`, `Quot.sound`; global lint reports only pre-existing unrelated unwired modules. Targeted arXiv audit found no source/Gamma/RH antecedent.

## Log

- 2026-09-01 — paper proof and Lean formalization complete.
