# Nonempty divisor marks cannot recover their prime-valued stratum

- **ID:** twin-prime-nonempty-divisor-mark-transfer
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `../1-in-progress/twin-prime-unconditional-programme-2026-10-23.md`
- **Statement attacked:** Proper-divisor marks approximating one on shifted
  primes also approximate one after restriction to prime-valued shifts.

## No-go closure

- **Exact killing mechanism:** Every such mark is zero at every prime.
  Therefore on every twin pair its squared error from one is exactly one.
  This is an obstruction to the proposed transfer, not a refutation of
  unrestricted shifted-prime cancellation or of any cited paper.
- **Strongest positive survivor:** The attainable minimum squared error
  over all proper-divisor marks is the twin-prime mass. Equality holds iff
  every positive-weight composite shift has mark one. The signed residual
  decomposition retains the composite contribution required for a lower bound.
- **Exact insight:** Improving the approximation yields upper control;
  the desired lower bound requires a positive signed surplus. This is known
  finite orthogonal decomposition, not a claimed advance in number theory.
- **Paper and Lean status:** complete. See
  [survivor proof and audit](../3-formalized/twin-prime-divisor-mark-transfer-boundary.md).
  Exact capstones: `TwinPrime.divisorMarkError_eq_twinMass_iff`,
  `TwinPrime.exists_divisorMark_minimum`, and
  `TwinPrime.twinMass_eq_signed_residual_difference`.
- **Novelty verdict:** survivor is `REDISCOVERED`; proposed transfer is `FALSE`.

## Second pass

Allow arbitrary real coefficients depending on both integer and divisor.
This enlarges the mark space beyond fixed small-prime interval marks and
still leaves the exact same forced prime error. Normalizing the count of
all nontrivial proper divisors attains the lower bound, so the full mark
space has no stronger universal squared-error obstruction. A lower bound
for this minimum would be a lower bound for twin mass itself, not an
independent input. The next route must retain arithmetic signs on a sifted
set and prove their estimate rather than assume it.

## Log

- 2026-10-23 — Retired after exact positive survivor passed paper and Lean audits.
