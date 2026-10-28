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
`../2-fully-proven/arithmetic-counting-prime-parity-ramanujan.md`. All seven
theorems in `PrimeParityRamanujanCoordinates.lean` now pass the kernel and
transitive axiom audit. Its olean is being written because the next harmonic
normalization module imports it. Canonical final source check remains.

`arithmetic-counting-maximal-gap-rigidity.md` records the still-unproved exact
endpoint. A two-mode spectral reduction now isolates its remaining analytic
and linear-algebra obligations. No maximal-gap claim is yet asserted.

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
- Remaining first batch: recover an explicit successful exit for the first
  leaf's canonical check (its earlier terminal result was lost at compaction); move
  `arithmetic-counting-pole-angle.md` to `3-formalized`; preserve the audit log.
  The failed-rule card with its strongest positive survivor is now in
  `5-failed/arithmetic-counting-submaximal-gap-selection.md`.
- Next exact proofs: `/tmp/acp-normalized-check.lean` (unit parity constraint,
  common harmonic normalization, exact mixed inner product, norm and residual
  limits) and `/tmp/acp-two-mode-check.lean` (homogeneous finite constrained-energy
  helper). These two scratch files have not been compiled yet.
- `/tmp/acp-ramanujan-check.log` now records seven successful axiom audits;
  `/tmp/acp-build-ramanujan.log` is the active olean command.
- The first four theorem axiom log is `/tmp/acp-axiom-audit.log`. Canonical logs
  are `/tmp/acp-final-correlation.log`, `/tmp/acp-final-sparse.log`,
  `/tmp/acp-final-parity.log`, `/tmp/acp-final-complete.log`. These are all finished.
- Research scope remains all source-report mechanisms and questions. Do not
  treat this first contribution as completion of the programme.
