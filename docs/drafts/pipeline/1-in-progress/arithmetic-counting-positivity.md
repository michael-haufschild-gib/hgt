# Arithmetic Counting Positivity

- **ID:** ACP-FOUNDATIONS
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** ../../../../docs/reports/review-2810/obstacles-summary.md, sections 2.7–2.8
- **Statement:** Develop independent arithmetic counts producing selective positivity, including all five mechanisms and structural questions in the source report.

## Goal

Own folder and umbrella `formal/GaloisForLFunctions/ArithmeticCountingPositivity`;
foundational README; significant unconditional Lean contributions; full research
scope preserved until the stated mechanisms and questions are resolved. Do not
use `hgtl7`. No numerical experiments or trusted computation proofs.

## Gates

- [x] 0 → 1: source report read; mathematical scope and countermodel battery specified.
- [ ] 1 → 2: dependency-closed paper proofs for individual contributions.
- [ ] 2 → 3: corresponding Lean theorems, foreground `lake --old env lean` audits,
  transitive `#print axioms` checks, umbrella wiring.
- [ ] Complete programme: selective overlap; arithmetic Herglotz; integer-side
  auxiliary counting; finite-rank renormalization; exact inertia counting;
  five structural questions answered; all calibrations and exhaustion proved.

## Approach

Start from exact arithmetic incidence counts, track the signed correlation they
retain, and audit parity twisting before any global positivity claim. Search the
corpus for the sharp walk gap, counting constructions and previously proved
obstructions. Give every new inequality an explicit scope and positive survivor.

## Current evidence

Foundational README and four-module first contribution written. The uniform
squared-correlation transfer, its sharp geometric projection bound, exact
prime-parity pairing, bounded boundary error, exact harmonic density and
positive prime-two gap are proved. Every submaximal threshold admits a
nontrivial completely multiplicative prime flip with untwisted polar matching
but a negative test for the literal complete Weil functional.

All 28 theorem axiom audits passed with only `propext`, `Classical.choice`,
and `Quot.sound`. All four canonical check logs have no diagnostics; the fourth
finished successfully. The final check caught a singleton-sum
simplification in the prime-three example, now fixed and rechecked.

The next bridge is the harmonic Ramanujan coordinate of prime parity:
an exact Mobius divisor identity and bounded decimation error imply that all
nontrivial conductors coprime to the flipped prime have zero limiting
correlation. Its closed proof is in
`../3-formalized/arithmetic-counting-prime-parity-ramanujan.md`. All seven
theorems in `PrimeParityRamanujanCoordinates.lean` now pass the kernel and
transitive axiom audit. Its olean was written because the next harmonic
normalization module imports it. The canonical final source check also passed.

The valuation-box branch is formalizing the maximal-gap theorem for primes
at least 11 in `LargePrimeFlipsAttainTheMaximalGap.lean`; its paper card is
`../2-fully-proven/arithmetic-counting-maximal-gap-rigidity.md`. The user
confirmed this as the intended endpoint and rejected the redundant independent
endpoint for primes at least 41. That draft and its separate two-mode helper
have been removed. Preserve the other researcher's valuation-box work.

The retained independent contribution is the exact bridge from parity counts
to squared coordinates on actual prime eigenlines. It is useful beyond the
maximal-gap application and must be finished on its own mathematical merits.

Existing worktree contains other researchers' changes; preserve them. The source report
is being updated concurrently: its inertia/mollifier proposal has changed into
a displacement-sensitive census question. Recheck current text and the relevant
counterexample before choosing that branch.

## Open obligations

All producer mechanisms remain open. An RH-equivalent or quasi-RH-equivalent
estimate is not an available input. Do not close this card merely because a
finite arithmetic construction or README is finished.

## Verification handoff

- Successful own oleans: `HarmonicCorrelationPaysThePrimeGap` and
  `SparsePrimeFlipsRetainPositiveGaps`, built only because subsequent own modules import them.
- `PrimeParityPairing.lean` now compiles and has its olean for the obstruction
  module. Its exact count, boundary error, harmonic limit and prime-two gap
  comparison are proved. Full-cone uniqueness has standard axioms only.
- All four initial leaves are wired into the own umbrella, and that umbrella
  is imported by `MainTheorems.lean`. No umbrella was compiled.
- The first batch is closed: all four canonical leaf checks exited zero
  without diagnostics. `arithmetic-counting-pole-angle.md` is now in
  `3-formalized`, with the durable audit report beside it.
  The failed-rule card with its strongest positive survivor is now in
  `5-failed/arithmetic-counting-submaximal-gap-selection.md`.
- Next exact proof: `/tmp/acp-normalized-check.lean` (unit parity constraint,
  common harmonic normalization, exact mixed inner product, norm and residual
  limits, and actual eigenline coordinates).
- `/tmp/acp-ramanujan-check.log` records seven successful axiom audits;
  `/tmp/acp-build-ramanujan.log` records its successful olean command. The
  fifth leaf passed its final canonical check without diagnostics.
- The missing imported `TheSimplePrimeEigenlinesConvergeToRamanujanLines`
  olean has built successfully alone, for the harmonic spectral bridge.
- `/tmp/acp-normalized-check.lean` now contains the full spectral-coordinate
  bridge: 14 public theorems, spectral projection error and norm limits,
  the orientation-independent squared coordinate, and actual simple
  eigenline coordinates. Its paper card is
  `../2-fully-proven/arithmetic-counting-harmonic-spectral-coordinates.md`.
  Its first check found only local algebra/rewrite issues, now corrected for
  another check. It includes all axiom commands. Do not accept the earlier
  failed audit's `sorryAx` entries; only a completely successful check counts.
- The abandoned `/tmp/acp-maximal-check.lean` and `/tmp/acp-two-mode-check.lean`
  were removed at the user's direction. Do not resume that endpoint or
  substitute it for the stronger valuation-box branch.
- The first four theorem axiom log is `/tmp/acp-axiom-audit.log`. Canonical logs
  are `/tmp/acp-final-correlation.log`, `/tmp/acp-final-sparse.log`,
  `/tmp/acp-final-parity.log`, `/tmp/acp-final-complete.log`. These are all finished.
- Research scope remains all source-report mechanisms and questions. Do not
  treat this first contribution as completion of the programme.
