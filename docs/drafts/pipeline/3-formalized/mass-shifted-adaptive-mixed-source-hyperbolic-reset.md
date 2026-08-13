# Mass-shifted adaptive mixed source hyperbolic reset

- **ID:** `mass-shifted-adaptive-mixed-source-hyperbolic-reset`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 Exact open core
- **Scientific status:** `[PROVED HERE] [CORPUS-NOVEL] [LEAN-PROVED] [EXTERNAL NOVELTY SEARCHED]`

## Result

Let `F_n` be weighted cumulative Jacobi flux, `U_n=F_n/(2n+1)` packet mean, `E_n` centered
packet energy, `G_n=1/U_n-y` reciprocal projective clock, and `J_n` literal drift-removed adaptive
mixed/completed `P^sharp` source action. Exact reserve is

```text
J_(n+1) - (E_(n+1)-E_n)
 = E_n + F_(n+1)^2/(2n+3)
   + 4 sum_(j<n+1) beta_j
   + 2(n+2)(beta_(n+1)+beta_(n+2)) > 0.
```

The online-variance identity and exact reciprocal-clock step therefore give

```text
(2n+1)(2n+3) U_n^2 U_(n+1)^2 (G_(n+1)-G_n)^2 < 2 J_(n+1).
```

On every physical right ray above an actual degree-`n+1` terminal frontier, terminal-chamber
Riccati positivity proves `U_n,U_(n+1)>0`; no mean-nonvanishing premise remains.

## Conjecture → proof/fail ledger

1. **Ordinary packet variance pays reciprocal-clock reset.** `[FALSIFIED]` Existing genuine
   positive-Jacobi reset counterfamily has bounded variance/spread but reset diverging like
   `1/epsilon`.
2. **Newborn source action pays raw Euclidean mean displacement.** `[PROVED BUT INCOMPLETE]`
   Source action strictly dominates packet-energy increment, which controls mean displacement.
3. **Same source pays reset after forced inverse-mean metric correction.** `[LEAN-PROVED]` Exact
   denominator cancellation yields hyperbolic reset law above.
4. **Pointwise hyperbolic payment closes RH.** `[FAILED / SHARP BOUNDARY]` It proves correct local
   metric and removes arbitrary reset, but one still needs a common all-degree integral source
   budget or a degree-uniform lower bound on adjacent means along parabolic frontier staircase.

## Higher principle

Degree renewal is Euclidean in Jacobi packet coordinates but singular after reciprocal
projectivization. Repeated scalar-clock failures are shadows of metric mismatch, not missing
orientation. Literal arithmetic action does pay renewal, but only in forced hyperbolic metric.
Thus remaining escape is exactly mean collapse/all-degree source non-tightness.

## Formal audit

Module:
`RHTower/XiShiftedCanonicalAdmissionAdaptiveMixedSourceHyperbolicReset.lean`.
It formalizes packet-energy nonnegativity, exact reserve, strict source domination, packet-mean/
normalized-flux identification, division-free hyperbolic payment, terminal-chamber discharge, and
actual frontier right-ray specialization. No computation, representing measure, RH premise,
fixed reporter, orientation map, reflection aggregation, or added axiom is used.
Direct `lake env lean` check and targeted module build pass. Axiom audit of eight capstones reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## Novelty audit

External search found online variance, Toda flows, and order-moment total positivity. Located
results either concern generic algebra or require positive representing weights unavailable before
RH. No literal shifted-Xi adaptive rational--Gamma-minus-von-Mangoldt source payment of a
reciprocal Jacobi reset was located. Priority remains provisional.

## Log

- 2026-08-13 — ordinary metric falsified; exact hyperbolic reserve and terminal-frontier source
  payment derived and formalized.
