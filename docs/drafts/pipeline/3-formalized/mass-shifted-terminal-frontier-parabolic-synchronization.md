# Mass-shifted terminal-frontier parabolic synchronization

- **ID:** `mass-shifted-terminal-frontier-parabolic-synchronization`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 Exact open core
- **Statement:** Canonical terminal frontiers inherit the corpus parabolic degree horizon, so every occupied degree-`n` frontier satisfies `tau_n <= K (n+2)^2`; false RH therefore forces cofinal strict frontiers on an intrinsic `sqrt(tau)=O(n)` schedule.

## Goal

Close upper degree--mass synchronization explicitly identified as missing by the cofinal-schedule
no-go.  Bridge source-generated canonical terminal frontiers to existing unconditional parabolic
Hankel positivity.  This does not by itself prove RH: remaining burden is a source-action estimate
uniform on this now-intrinsic parabolic diagonal.

## Gates

- [x] 0 → 1 in-progress: source-pure statement, attack, falsifiers, and corpus dependencies identified
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone proof and novelty review

## Conjecture → proof/fail ledger

1. **Fixed-degree recession supplies upper synchronization.** `[FALSIFIED]` Pointwise eventual
   positivity admits arbitrarily delayed diagonal schedules; corpus has an exact delayed-switch
   countermodel.
2. **Parabolic degree horizon bounds canonical terminal frontiers.** `[LEAN-PROVED]` Above
   `K(n+2)^2`, every nonzero vector has positive shifted-Xi Hankel quadratic, hence block
   `H_(n+2)` is positive definite.  Every member of its failure set is therefore below this bound;
   taking the supremum proves same bound for `tau_n`.
3. **False RH has an arbitrary-rate frontier escape.** `[FALSIFIED]` Cofinal strict-frontier
   renewal plus preceding bound forces the actual escape into the parabolic cone.  Arbitrarily
   delayed far-right positive schedules are irrelevant because they are not canonical frontiers.
4. **Parabolic synchronization closes RH.** `[FAILED / SHARP BOUNDARY]` It removes nonproper mass
   escape but does not yet bound adaptive mixed/completed source action uniformly in simultaneous
   degree and mass.  Remaining theorem is parabolic-diagonal source-action properness.

## Dependency-closed proof `[LEAN-PROVED]`

Let `K=routeUParabolicDegreeHorizon`.  Corpus PDH states that for any `d`, any nonzero
`c : Fin(d+1) -> R`, and any `y >= K(d+1)^2`, shifted-Xi reciprocal Hankel quadratic is positive.
Take `d=n+1`.  Matrix/quadratic identification and Hermitian symmetry imply

```text
y >= K(n+2)^2  ==>  H_(n+2)(y) > 0.
```

Thus every `y` in canonical failure set `B_n={y>=0 : H_(n+2)(y) not > 0}` satisfies
`y < K(n+2)^2`.  Since `B_n` is bounded and occupied, supremum characterization gives

```text
tau_n = sup B_n <= K(n+2)^2.
```

At an actual strict successor, frontier attainment makes the inequality strict.  If RH is false,
existing source-adaptive frontier renewal gives, above every mass floor `A`, an occupied strict
step with

```text
A < tau_n < tau_(n+1) < K(n+3)^2.
```

Hence actual counterphase lies on intrinsic parabolic degree--mass schedule.  QED.

## Lean certificate

Module:
`formal/GaloisForLFunctions/RHTower/XiShiftedTerminalFrontierParabolicSynchronization.lean`.

Capstones:

- `xiShiftedMomentHankelMatrix_posDef_of_parabolicDegreeHorizon`;
- `lt_parabolicDegreeHorizon_of_mem_xiShiftedHigherBlockFailureSet`;
- `xiShiftedHigherBlockTerminalFrontier_le_parabolicDegreeHorizon`;
- `sqrt_xiShiftedHigherBlockTerminalFrontier_le_linearDegreeHorizon`;
- `xiShiftedHigherBlockTerminalFrontier_succ_lt_parabolicDegreeHorizon`;
- `exists_cofinal_sourceAdaptive_parabolicFrontierCertificate_of_not_riemannHypothesis`.

Direct Lean check and targeted module build pass.  Axiom audit of all capstones reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-13 — bridge discovered by joining canonical frontier renewal to pre-existing PDH; card opened.
- 2026-08-13 — paper proof frozen, formalized, wired into `RHTower.lean`, targeted build and axiom audit passed.
