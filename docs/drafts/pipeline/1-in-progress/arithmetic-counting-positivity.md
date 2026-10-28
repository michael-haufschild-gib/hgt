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

First foundational README written. `HarmonicCorrelationPaysThePrimeGap.lean`
has compiled successfully: uniform squared-correlation prime-gap bound and
sharpness of its underlying projection inequality. Its two analytic inputs
have transitive axiom sets exactly `propext`, `Classical.choice`, `Quot.sound`.
`SparsePrimeFlipsRetainPositiveGaps.lean` also compiles: every threshold below
`2 log 2` admits a nontrivial completely multiplicative prime flip with that
gap and untwisted polar matching. The sharper parity-pairing count and the
complete-Weil obstruction are being formalized in the same folder.
The dependency-closed paper proof is on
`../2-fully-proven/arithmetic-counting-pole-angle.md`.

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
- Remaining: check the complete-source obstruction module; audit all new axioms; run final canonical
  `lake --old env lean <file>` on each finished leaf; finish umbrella imports;
  move the individual theorem card to `3-formalized`; create the failed-rule
  card with its positive survivor; update README mathematical pillars.
- Research scope remains all source-report mechanisms and questions. Do not
  treat this first contribution as completion of the programme.
