# Lean claim review row #78 — Weil functional equation of the L-polynomial

- **ID:** lean-claim-review-row-078-weil-fe-l-polynomial
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/00-status.md · 00-status row #78; ../../door/bucket-ledger-footholds.md
- **Claimed ledger status:** `THEOREM (Lean)`; no matching ticket is present in `../3-formalized/` as of 2026-06-19.
- **Statement:** Weil functional equation of the L-polynomial.

## Goal
Audit the claim from scratch. Researchers must distinguish the finite multiset/self-dual polynomial algebra from the full imported Weil theorem over function fields. Leaner checks the formalization only after that scope is fixed.

## Claimed Lean footholds to verify
- `formal/GaloisForLFunctions/FunctionFieldFE.lean`
- Candidate names: `functionField_esymm_FE`, `functionField_localFactor_FE`, `multiset_esymm_map_mul`

These names are leads, not certification.

## Gates
- [ ] 0 -> 1 in-progress: researcher assigned; clarify whether the row asserts algebraic FE skeleton or full Weil theorem
- [ ] 1 -> 2 fully-proven: researchers confirm the complete paper proof for the scoped statement
- [ ] 2 -> 3 formalized: Leaner verifies exact theorem names by scratch file, `lake build` green, `scripts/check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone proof note plus Lean certificate

## Approach
Review the reciprocal-root multiset algebra behind the local factor functional equation, then compare that finite algebraic skeleton to the stronger function-field theorem named in the row.

## Log
- 2026-06-19 — created in 0-backlog as a claim-review ticket for an un-ticketed `THEOREM (Lean)` ledger row.
