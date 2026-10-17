# Signed optimal collar compensation for packet transport

- **ID:** signed-prime-polar-optimal-collar
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** `1-in-progress/signed-prime-polar-transport-2026-10-17.md`
- **Count:** contribution 7; one complete package.

## Target

The previous upper bound fixes coefficient 1 in f=g+(f-g). Permit every real
coefficient t, retaining the sign of C=∫fg. For η=exp(c), R=||f||², B=||g||²,
M=mass N, and the admitted correlation-based upper bound U for ||P_N(g)||²,
the actual source split gives

Q_N(f) ≤ F(t)=(1+η)t²U+(1+1/η)M²(R-2tC+t²B).

Put D=(1+η)U+(1+1/η)M²B and E=(1+1/η)M²C.
Construct t*=E/D and prove, including D=0,

F(t)-[(1+1/η)M²R-E²/D]=D(t-t*)².

Classify every minimizer and transfer the optimized upper certificate to global
signed Chebyshev transport. Cap by M²R to retain the original mass bound.
At c=0, compare with contribution 6 using t=1. No source, covariance, or
denominator nonvanishing premise is allowed in the main endpoints.

## Proof plan

- [x] Search actual corpus and inspect weighted packet splitting, collar gauge
  budget, source residual energy and source Gram precedents.
- [x] Check targeted optimization search; exclude equivalent existing endpoints.
  Both searches partial=false/errors=[]; coverage snapshot, many compiler entries
  pending/stale. Retrieved finite-partition Gram optimization differs from this
  actual collar compensation family. No external novelty claim.
- [x] Write dependency-closed paper proof, especially the zero-denominator case:
  `docs/reports/BiScaleUncertainty/SignedPrimePolarOptimalCollar.md`.
- [x] Prove source scaling, exact signed remainder energy, and trial upper bound.
  `SignedPrimePolarScaledCollar.lean` passes direct `lake --old env lean` with
  empty diagnostics (`/tmp/spp7-scaled-build.log`).
- [x] Prove explicit optimizer, exact excess, minimizer classification, comparisons,
  and exact strict-improvement threshold. `SignedPrimePolarOptimalCollar.lean`
  passes its final direct leaf check with empty diagnostics (`/tmp/spp7-optimal-build.log`).
- [x] Transfer global coherent and Lévy transport; audit signatures and axioms.
  `/tmp/spp7_final_axioms.lean` passes: twelve endpoint reports contain only
  propext, Classical.choice, Quot.sound; main signatures have only actual sources
  and numerical parameters. Both final leaf checks have empty diagnostics.
- [x] Wire imports, lint/index, promote card, update facts and memory.
  Index refresh exits 0. Lint exits 1 solely for six unrelated concurrent wiring
  errors, listed in the facts ledger; no task-local errors. Evidence:
  `/tmp/spp7-final-axioms.log`, `/tmp/spp7-index.log`, `/tmp/spp7-lint.log`.

The elementary quadratic minimization is an input. The intended contribution is
an actual signed-source compensation certificate, exact degeneracy handling,
and a provably no-worse global transport budget. No cutoff-uniform conclusion.
README remains read-only; no RH work or numerical experiments.
