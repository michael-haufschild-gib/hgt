# Shifted-pole separation for the triangular Möbius head

- **ID:** MC-C12.99-S1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `HardyTheorem`, `XiEntireReal`, `ZetaLogDerivResidue`.
- **Parent:** `../1-in-progress/mc-triangular-quadratic-pole-cancellation.md`.
- **Lean:** `formal/GaloisForLFunctions/RHTower/LiouvilleTriangularPoleSeparation.lean`.

## Exact unconditional result

There is a complex w with `3/4 <= Re(w) < 1`, nonzero imaginary part, and

```
zeta(2w-1) = 0,
zeta(w) != 0,
zeta(2w-1/2) != 0.
```

Write `U(s)=(s-1)zeta(s)`, continued by U(1)=1. At one such w, for **every** complex a,b,d,

```
Q_(a,b,d)(s) = d*zeta(2s)/(s*U(s))
              + a/U(2s-1)
              + b*(2s-3/2)/((s-1/2)*U(2s-1/2))

AnalyticAt Q_(a,b,d) w  <->  a=0.
```

Both existential statements have no supplied zero, zero-free, cancellation, simplicity, growth, or RH hypothesis. Zero multiplicities need not be known.

Public theorems:

- `RHTower.LiouvilleTriangularPoleSeparation.exists_separated_pole`.
- `RHTower.LiouvilleTriangularPoleSeparation.exists_pole_coefficient_rigidity`.

## Proof

Hardy's theorem supplies rho=1/2+i*gamma, gamma!=0. If every zero in the closed right half-strip had another zero at (rho+1)/2, all points `rho_n=1+(rho-1)/2^n` would be zeros. They remain in that half-strip, retain nonzero imaginary part, and tend to1. Continuity of U and U(1)=1 contradict U(rho_n)=0. Hence at some zero the half-shift w is not a zero. The other shifted argument `2w-1/2=rho+1/2` lies on or right of Re=1, where zeta is nonzero.

The analytic function `s -> U(2s-1)` vanishes at w but is not locally identically zero: an identity theorem would contradict its value1 at s=1. Its reciprocal is therefore not continuous at w. The other two terms of Q are analytic there, because their denominators are nonzero and zeta(2s) is regular. Subtracting them shows that analyticity of Q forces a=0. Conversely, a=0 leaves exactly those two analytic terms.

## What this does and does not resolve

In the parent paper decomposition of `F_c=P+c*A`, the three coefficients are `a=2*c*Z`, `b=-2*c`, `d=1`, and the remaining transform is c times a holomorphic remainder on Re(s)>1/2. Thus this is the analytic separation step needed to exclude an uncancelled actual short head. It is not yet a Lean Mellin identity for F_c: that source connection, its remainder regularity and the Landau sign argument are still pending in the parent card.

The actual short quadratic term B has not been proved oscillatory in Lean by this module. No separate-payment no-go is retired here. The RH-critical lower bound for the complete P=2A-B remains unproved.

## Verification (2026-10-04, turn1005s)

- Targeted `lake --old build GaloisForLFunctions.RHTower.LiouvilleTriangularPoleSeparation`: exit0, leaf built in146s. Reported10064 dependency jobs, with cached diagnostics replayed; no full or umbrella build requested.
- Required `lake --old env lean GaloisForLFunctions/RHTower/LiouvilleTriangularPoleSeparation.lean`: exit0, no diagnostics.
- Corrected `/tmp` axiom/API audit: exit0. Both public theorems report only `propext`, `Classical.choice`, `Quot.sound`. An earlier scratch driver had universe-inference errors in extra API checks; no theorem or proof changed to fix that driver.
- Unique RHTower umbrella import added. Index regeneration exit0; three public API entries verified.
- Global lint exit1:16 unrelated unreachable modules, none in this leaf; existing large-file warnings. This is not a clean global-lint claim.
- No numerical experiment, added axiom, placeholder, heartbeat increase, subagent, full build, commit or push.

## Source audit

The parent records the documented pole-cascade search and its freshness. A further documented deep search for `Mellin weighted harmonic partial sums square root cutoff integral LSeries` completed exit0, partial=false:65322 files, compiled43, stale2660, pending49255; snapshot/current1224337/1224338, query index1224331; older-generation warning, semantic coverage unmeasured, background refresh incomplete. Candidate lemmas, source arguments, empty proof ideas and ingredient sets inspected. `LSeries_eq_mul_integral` and `StepProfileMellinLSeries` are relevant to the pending source connection, but were not imported as a proof of that connection.
