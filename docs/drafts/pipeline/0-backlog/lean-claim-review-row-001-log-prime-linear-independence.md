# Lean claim review row #1 — log-prime linear independence

- **ID:** lean-claim-review-row-001-log-prime-linear-independence
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/00-status.md · 00-status row #1; ../../door/bucket-ledger-footholds.md
- **Claimed ledger status:** `THEOREM (Lean)`; no matching ticket is present in `../3-formalized/` as of 2026-06-19.
- **Statement:** `{log p}` are Q-linearly independent.

## Goal
Audit the claim from scratch. Researchers first decide whether the mathematical statement and proof are valid without trusting the ledger tag. Only after that review should Leaner check whether the claimed Lean formalization really exists in this toolchain.

## Claimed Lean footholds to verify
- `formal/GaloisForLFunctions/Core.lean`
- Candidate names: `logPrime_linearIndependent_int`, `linearIndependent_log_primes`

These names are leads, not certification.

## Gates
- [ ] 0 -> 1 in-progress: researcher assigned; statement restated precisely; no reliance on the old `THEOREM (Lean)` ledger label
- [ ] 1 -> 2 fully-proven: researchers produce or confirm a complete paper proof from scratch
- [ ] 2 -> 3 formalized: Leaner verifies exact theorem names by scratch file, `lake build` green, `scripts/check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone proof note plus Lean certificate

## Approach
Start with unique factorization and the map from finitely supported integer prime exponents to products of primes. Then verify the passage from integer relations to Q-linear independence over real logarithms.

## Log
- 2026-06-19 — created in 0-backlog as a claim-review ticket for an un-ticketed `THEOREM (Lean)` ledger row.
