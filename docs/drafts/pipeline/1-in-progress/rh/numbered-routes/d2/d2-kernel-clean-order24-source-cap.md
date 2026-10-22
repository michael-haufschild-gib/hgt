# D2 kernel-clean order-24 source cap

- **ID:** `d2-kernel-clean-order24-source-cap`
- **Stage:** 1 — in progress
- **Type:** CONJECTURE / unconditional source cap and sixth-trace height theorem (Lean)
- **Source route:** D2 plus centered order-24 sixth reciprocal trace
- **Statement:** Replace the native-decision first-atom quadrature leaf by a standard-kernel
  rational certificate, yielding `normalizedPrimeArchMoment 2 < 3/10000000` and the order-24
  sixth-trace off-line height exclusion.

## Goal

Close the sole nonstandard-axiom dependency in the corpus's strongest sixth-trace source cap.
The existing analytic enclosure and tail proof are kernel-clean; only evaluation of five finite
rational inequalities currently uses `native_decide`. A standard-kernel proof would promote the
conditional order-24 finite reduction to an unconditional RH verified-height advance and then to
a stronger D2 threshold.

## Gates

- [x] 0 → 1 in-progress: exact open leaf isolated; source-pure attack and route passport
- [ ] 1 → 2 fully-proven: dependency-closed paper proof and rational certificate
- [ ] 2 → 3 formalized: closed Lean theorem, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem note and independent expert audit

## Conjecture and attack

The existing analytic quadrature reduces the source cap to five rational inequalities:

```text
0.4969488 < a0,
0.02297 < a1 < 0.0229718,
0.0029627 < a2,
a3 < 0.00059935,
```

where `aj = thetaCuspAtomRawEvenMoment j 1`. Their current finite certificate is proved by
`native_decide`, whose generated axiom is inadmissible for this route.

Conjecture: the same five inequalities admit a feasible proof using only kernel-reduced rational
identities. Factor every interval mass into its recursively rounded endpoint weight and a local
unit polynomial mass; prove `QPoly` scaling and integration linearity once; then normalize bounded
blocks rather than one monolithic 64-cell expression. Explicitly expose `Rat.floor_def` and
`Rat.ceil_def` so endpoint recurrences reduce in the kernel.

Once closed, reuse the existing analytic interval comparison and tail bound to prove

```text
normalizedPrimeArchMoment 2 < 3/10000000.
```

Feed that cap into the existing centered order-24 sixth-trace atom floor and quartet domination.
The expected positive survivor is the unconditional exclusion of every off-line Xi zero below
squared height `467/2`, followed by the largest exact rational D2 threshold whose shifted square
lies below that height.

## Current proof state

- Proved in Lean scratch: `QPoly.scale_add`, `scale_scale`, left/right compatibility of `mul` with
  `scale`, `momentMass_scale`, `integralMass_scale`, and endpoint-factorization of `lowerMass`.
- Diagnosed exact reducer obstruction: `roundDown` does not normalize efficiently until
  `Rat.floor_def` is unfolded; a one-cell endpoint calculation then closes in the kernel.
- Monolithic polynomial convolution remains too costly, so next proof surface is bounded block
  certificates with shared endpoint recurrence.
- No tree Lean module exists yet; scratch only.

## Novelty and literature audit status

Corpus search found the analytic quadrature, conditional order-24 reduction, and native-decision
leaf, but no standard-kernel proof of the five inequalities and no unconditional order-24 height
theorem. External primary-source audit is deferred until the mathematical and Lean certificate
close.

## Log

- 2026-08-28 — Isolated native-decision axiom as sole order-24 source-cap blocker.
- 2026-08-28 — Proved algebraic endpoint-factorization infrastructure in standard Lean scratch.
- 2026-08-28 — Opened kernel normalization attack using explicit rational floor/ceiling reduction
  and bounded block certificates.
- 2026-08-28 — One-cell endpoint reduction closes after exposing `Rat.floor_def`, but the
  monolithic 64-cell `QPoly` normalization failed to elaborate within a practical foreground
  proof window. This is a proof-term/normalizer scaling failure, not evidence against the five
  rational inequalities; route remains open. Next attack must share endpoint recurrences and
  normalize bounded blocks or use a small kernel-checked certificate language.
- 2026-08-28 — Extracted a positive survivor while this branch remains open: exact optimization of
  the kernel-clean order-23 atom endpoint proves the off-line height gap `Im(q)^2 ≥ 431349/2000`
  and advances D2 to `141858/10000`. See
  `d2-order23-endpoint-optimization.md` and
  `PrimeArchLogHeightDefectOrderTwentyThreeEndpointOptimization.lean`.
