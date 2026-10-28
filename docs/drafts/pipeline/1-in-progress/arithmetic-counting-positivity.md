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
to squared coordinates on actual prime eigenlines. It is now formalized in
`HarmonicParitySpectralCoordinates.lean`: all 14 public theorems pass the
transitive axiom audit, and the canonical installed-source check exited zero
without diagnostics. Its paper and durable audit are in
`../3-formalized/arithmetic-counting-harmonic-spectral-coordinates.md` and
the adjacent audit file. This closes six own leaves, with 49 public theorems.

Existing worktree contains other researchers' changes; preserve them. The source report
is being updated concurrently: its inertia/mollifier proposal has changed into
a displacement-sensitive census question. Recheck current text and the relevant
counterexample before choosing that branch.

## Open obligations

All producer mechanisms remain open. An RH-equivalent or quasi-RH-equivalent
estimate is not an available input. Do not close this card merely because a
finite arithmetic construction or README is finished.

## Verification handoff

- Six own leaves are installed, individually checked, axiom-audited, and
  wired into `ArithmeticCountingPositivity.lean`. That umbrella is imported
  by `MainTheorems.lean`; no umbrella was compiled.
- Durable proof and audit records are the three `3-formalized` cards
  `arithmetic-counting-pole-angle.md`,
  `arithmetic-counting-prime-parity-ramanujan.md`, and
  `arithmetic-counting-harmonic-spectral-coordinates.md`, with their adjacent
  `-audit.txt` files. All final canonical checks exited zero without
  diagnostics; all theorem audits have only the three standard axioms.
- Own oleans exist for `HarmonicCorrelationPaysThePrimeGap`,
  `SparsePrimeFlipsRetainPositiveGaps`, `PrimeParityPairing`, and
  `PrimeParityRamanujanCoordinates`, because later own leaves import them.
  Neither the complete-Weil obstruction nor the spectral-coordinate leaf
  required its own olean. The missing imported
  `TheSimplePrimeEigenlinesConvergeToRamanujanLines` olean was built alone.
- Completed scratch files and transient logs have been removed after their
  evidence was preserved in the durable audit records. The abandoned
  maximal-gap and two-mode drafts are also removed. Do not recreate the
  redundant prime-41 endpoint.
- The active extension is on
  `../2-fully-proven/arithmetic-counting-finite-flip-exhaustion.md`.
  Corpus searches found no arbitrary finite-prime harmonic law; the
  existing finite-flip Mertens matching law is distinct. Its closed
  bounded-error recurrence proof is on
  `../2-fully-proven/arithmetic-counting-finite-prime-density.md`.
- `/tmp/acp-finite-density-check.lean` contains the complete first draft:
  product density, exact prime-insertion recurrence, bounded error, exact
  limit, and paid gap. Its first check 3693 exited one: two unfolding issues,
  the renamed triangle inequality, and a neighborhood-order orientation.
  These are fixed. Check session 36694 is running, with log
  `/tmp/acp-finite-density-check.log`. Resume that handle before starting
  another Lean process. No new theorem from this draft is yet accepted.
- `/tmp/acp-finite-exhaustion-check.lean` contains the subsequent five-theorem
  draft: exact agreement with Liouville below the cutoff, eventual pointwise
  equality, positive matched finite stages, and failure of a uniform positive
  gap even on a cofinal rectangle of prime cutoffs and horizons. It imports
  the future `FinitePrimeFlipsHavePositiveHarmonicDensity.lean`; finish and
  audit that source, then build its first required olean before checking
  the exhaustion draft. Its paper card has moved to `2-fully-proven`.
- Corpus and mathlib leads used for that draft were inspected in source:
  `ArithmeticFunction.cardFactors_eq_sum_factorization`,
  `Nat.support_factorization`, `Finset.prod_pow_eq_pow_sum`,
  `Nat.mem_primeFactors`, `Nat.mem_primesBelow`, and `atomicWeilForm_congr`.
  The positive count must be finished before closing the exhaustion
  obstruction. Failed search calls were retried with exact names; no
  missing lemma is being treated as a proved input.
- Research scope remains all source-report mechanisms and questions. No
  part of the current batch completes the full programme.
